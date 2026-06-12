use std::fs;
use std::io::{Cursor, ErrorKind};
use std::ops::Deref;

use binrw::{BinRead, BinReaderExt, BinWrite};
use object::{Object, ObjectSymbol};
use sysinfo::{Pid, Process};

use super::Result;
use super::platform::Platform;

const EXE_PREFIX: &str = "pcsx2";
const EE_MEM_SYMBOL: &str = "EEmem";
// first 1MB is reserved for the kernel
const EE_MIN_ADDRESS: usize = 0x100000;
const EE_MEM_SIZE: usize = 0x2000000;

// Platform-specific access to another process's address space. On Unix this is backed by
// `/proc/{pid}/mem`; on Windows by a process handle and Read/WriteProcessMemory.
#[cfg(unix)]
mod platform_mem {
    use std::fs::{File, OpenOptions};
    use std::io::{self, BufRead, BufReader};
    use std::os::unix::fs::FileExt;
    use std::path::Path;

    use sysinfo::Pid;

    use super::Result;

    pub struct MemoryHandle {
        memory: File,
    }

    impl MemoryHandle {
        pub fn open(pid: Pid) -> Result<Self> {
            let memory = OpenOptions::new()
                .read(true)
                .write(true)
                .open(format!("/proc/{pid}/mem"))?;
            Ok(Self { memory })
        }

        pub fn read_at(&self, buf: &mut [u8], address: u64) -> io::Result<()> {
            self.memory.read_exact_at(buf, address)
        }

        pub fn write_at(&self, data: &[u8], address: u64) -> io::Result<()> {
            self.memory.write_all_at(data, address)
        }
    }

    // Find the base address at which `exe_path` is mapped into process `pid`.
    pub fn find_module_base(pid: Pid, exe_path: &Path) -> Option<u64> {
        let exe_path = exe_path.to_string_lossy();
        let memory_map = BufReader::new(File::open(format!("/proc/{pid}/maps")).ok()?);
        for line in memory_map.lines() {
            let line = line.ok()?;
            let parts: Vec<_> = line.split_whitespace().collect();
            if parts.len() != 6 {
                continue;
            }

            if parts[5] == exe_path {
                return u64::from_str_radix(parts[0].split('-').next()?, 16).ok();
            }
        }

        None
    }
}

#[cfg(windows)]
mod platform_mem {
    use std::ffi::c_void;
    use std::io;
    use std::path::Path;

    use sysinfo::Pid;
    use windows_sys::Win32::Foundation::{CloseHandle, HANDLE, INVALID_HANDLE_VALUE};
    use windows_sys::Win32::System::Diagnostics::Debug::{
        ReadProcessMemory, WriteProcessMemory,
    };
    use windows_sys::Win32::System::Diagnostics::ToolHelp::{
        CreateToolhelp32Snapshot, MODULEENTRY32W, Module32FirstW, TH32CS_SNAPMODULE,
        TH32CS_SNAPMODULE32,
    };
    use windows_sys::Win32::System::Threading::{
        OpenProcess, PROCESS_VM_OPERATION, PROCESS_VM_READ, PROCESS_VM_WRITE,
    };

    use super::Result;

    pub struct MemoryHandle {
        process: HANDLE,
    }

    impl MemoryHandle {
        pub fn open(pid: Pid) -> Result<Self> {
            // SAFETY: OpenProcess is a simple FFI call; we validate the returned handle below.
            let process = unsafe {
                OpenProcess(
                    PROCESS_VM_READ | PROCESS_VM_WRITE | PROCESS_VM_OPERATION,
                    0,
                    pid.as_u32(),
                )
            };
            if process.is_null() {
                return Err(io::Error::last_os_error().into());
            }
            Ok(Self { process })
        }

        pub fn read_at(&self, buf: &mut [u8], address: u64) -> io::Result<()> {
            let mut bytes_read = 0usize;
            // SAFETY: `buf` is a valid, writable slice of length `buf.len()`.
            let ok = unsafe {
                ReadProcessMemory(
                    self.process,
                    address as *const c_void,
                    buf.as_mut_ptr().cast::<c_void>(),
                    buf.len(),
                    &mut bytes_read,
                )
            };
            if ok == 0 || bytes_read != buf.len() {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        }

        pub fn write_at(&self, data: &[u8], address: u64) -> io::Result<()> {
            let mut bytes_written = 0usize;
            // SAFETY: `data` is a valid, readable slice of length `data.len()`.
            let ok = unsafe {
                WriteProcessMemory(
                    self.process,
                    address as *mut c_void,
                    data.as_ptr().cast::<c_void>(),
                    data.len(),
                    &mut bytes_written,
                )
            };
            if ok == 0 || bytes_written != data.len() {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        }
    }

    impl Drop for MemoryHandle {
        fn drop(&mut self) {
            // SAFETY: `self.process` is a valid handle obtained from OpenProcess.
            unsafe {
                CloseHandle(self.process);
            }
        }
    }

    // Find the base address at which `exe_path` is loaded in process `pid`.
    pub fn find_module_base(pid: Pid, _exe_path: &Path) -> Option<u64> {
        // SAFETY: the snapshot handle is validated and closed before returning.
        unsafe {
            let snapshot =
                CreateToolhelp32Snapshot(TH32CS_SNAPMODULE | TH32CS_SNAPMODULE32, pid.as_u32());
            if snapshot == INVALID_HANDLE_VALUE {
                return None;
            }

            let mut entry: MODULEENTRY32W = std::mem::zeroed();
            entry.dwSize = size_of::<MODULEENTRY32W>() as u32;
            // The first module in the snapshot is always the process's own executable, which is
            // the module whose symbols we resolved against.
            let base = if Module32FirstW(snapshot, &mut entry) != 0 {
                Some(entry.modBaseAddr as u64)
            } else {
                None
            };

            CloseHandle(snapshot);
            base
        }
    }
}

use platform_mem::{MemoryHandle, find_module_base};

pub struct Emulator {
    memory: MemoryHandle,
    ee_mem_base: usize,
    pid: Pid,
}

impl Emulator {
    fn try_get_emulator_from_process(pid: Pid, process: &Process) -> Option<Self> {
        let exe_path = process.exe()?;
        let lc_exe_name = exe_path.file_name()?.to_string_lossy().to_lowercase();

        if !lc_exe_name.starts_with(EXE_PREFIX) {
            return None;
        }

        // search for EEmem symbol
        // TODO: error handling
        let data = fs::read(exe_path).ok()?;
        let file = object::File::parse(&*data).ok()?;
        // `relative_address_base` is the image base for PE and 0 for ELF, so subtracting it
        // converts a symbol's address into an offset relative to the module's load address.
        let relative_base = file.relative_address_base();
        for symbol in file.symbols() {
            if !matches!(symbol.name().map(|name| name == EE_MEM_SYMBOL), Ok(true)) {
                continue;
            }

            // we've found the PCSX2 process; now find the start of EE memory
            let module_base = find_module_base(pid, exe_path)?;
            let ee_mem_ptr = symbol.address() - relative_base + module_base;

            let memory = MemoryHandle::open(pid).ok()?;
            let mut buf = [0u8; 8];
            memory.read_at(&mut buf, ee_mem_ptr).ok()?;
            let ee_mem_base = usize::from_le_bytes(buf);
            return Some(Self {
                memory,
                ee_mem_base,
                pid,
            });
        }

        None
    }

    pub fn search_for_emulator(platform: impl Deref<Target = Platform>) -> Option<Self> {
        for (pid, process) in platform.active_processes() {
            if let Some(emulator) = Self::try_get_emulator_from_process(pid, process) {
                return Some(emulator);
            }
        }

        None
    }

    pub fn pid(&self) -> Pid {
        self.pid
    }

    pub const fn is_address_valid(address: usize, size: usize) -> bool {
        address >= EE_MIN_ADDRESS && (address + size) <= EE_MEM_SIZE
    }

    pub fn read_memory(&self, address: usize, size: usize) -> Result<Vec<u8>> {
        if address.saturating_add(size) > EE_MEM_SIZE {
            return Err(std::io::Error::new(
                ErrorKind::UnexpectedEof,
                "attempt to read past end of EE memory",
            )
            .into());
        }

        let mut buf = vec![0u8; size];
        self.memory
            .read_at(&mut buf, (self.ee_mem_base + address) as u64)?;
        Ok(buf)
    }

    pub fn read<'a, T: BinRead<Args<'a> = ()>>(&self, address: usize, size: usize) -> Result<T> {
        self.read_args(address, size, ())
    }

    pub fn read_args<T: BinRead>(
        &self,
        address: usize,
        size: usize,
        args: T::Args<'_>,
    ) -> Result<T> {
        let data = self.read_memory(address, size)?;
        let value = Cursor::new(data).read_le_args(args)?;
        Ok(value)
    }

    pub fn write_memory(&self, address: usize, data: &[u8]) -> Result<()> {
        if address.saturating_add(data.len()) > EE_MEM_SIZE {
            return Err(std::io::Error::new(
                ErrorKind::UnexpectedEof,
                "attempt to write past end of EE memory",
            )
            .into());
        }

        self.memory
            .write_at(data, (self.ee_mem_base + address) as u64)?;
        Ok(())
    }

    pub fn write<T: for<'a> BinWrite<Args<'a> = ()>>(
        &self,
        address: usize,
        value: &T,
    ) -> Result<()> {
        self.write_args(address, value, ())
    }

    pub fn write_args<'a, T: BinWrite>(
        &self,
        address: usize,
        value: &T,
        args: T::Args<'a>,
    ) -> Result<()> {
        let mut buf = Cursor::new(Vec::new());
        value.write_le_args(&mut buf, args)?;
        self.write_memory(address, &buf.into_inner())?;
        Ok(())
    }
}
