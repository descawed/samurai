use std::fs;
use std::io::{Cursor, ErrorKind};
use std::ops::Deref;

use binrw::{BinRead, BinReaderExt, BinWrite};
use object::{Object, ObjectSymbol};
use sysinfo::{Pid, Process};

use super::Result;
use super::platform::Platform;

const PCSX2_EXE_PREFIX: &str = "pcsx2";
const EE_MEM_SYMBOL: &str = "EEmem";
// first 1MB is reserved for the kernel
const EE_MIN_ADDRESS: usize = 0x100000;
const EE_MEM_SIZE: usize = 0x2000000;

const PPSSPP_EXE_PREFIX: &str = "ppsspp";
// Masking a PSP virtual address folds the uncached (0x4xxxxxxx) and kernel (0x8xxxxxxx/0xCxxxxxxx)
// mirrors onto the canonical cached mapping, matching how PPSSPP itself resolves addresses.
const PSP_ADDRESS_MASK: usize = 0x3FFFFFFF;
const PSP_VRAM_BASE: usize = 0x04000000;
const PSP_RAM_BASE: usize = 0x08000000;
// the low 8MB of RAM is kernel and volatile memory; game data lives in user memory above it
const PSP_USER_MIN_ADDRESS: usize = 0x08800000;
const PSP_RAM_MAX_SIZE: usize = 0x04000000;
// PPSSPP maps RAM in pieces of at most 31MB (its MAX_MMAP_SIZE) that are contiguous in both
// address space and backing-file offset, so the OS may or may not coalesce them. The main RAM
// view is therefore the only mapping at least this large.
const PSP_RAM_VIEW_MIN_SIZE: u64 = 31 * 1024 * 1024;
// spacing between the cached RAM view and its uncached/kernel mirrors in host address space
const PSP_MIRROR_STRIDE: u64 = 0x40000000;

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

    // Collect the mappings of PPSSPP's emulated-memory arena in process `pid`. PPSSPP allocates
    // the arena with shm_open (name "/ppsspp_<N>.ram", falling back to a tmpfs file named
    // gc_mem.tmp) and unlinks it immediately, so its views appear as shared mappings of a
    // deleted file.
    pub fn psp_arena_candidates(pid: Pid, _memory: &MemoryHandle) -> Vec<(u64, u64)> {
        let Ok(file) = File::open(format!("/proc/{pid}/maps")) else {
            return Vec::new();
        };

        let mut regions = Vec::new();
        for line in BufReader::new(file).lines() {
            let Ok(line) = line else {
                break;
            };
            let parts: Vec<_> = line.split_whitespace().collect();
            // the trailing " (deleted)" makes for one more field than in find_module_base
            if parts.len() != 7 || parts[1] != "rw-s" || parts[6] != "(deleted)" {
                continue;
            }

            let is_arena_file = Path::new(parts[5])
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    (name.starts_with("ppsspp_") && name.ends_with(".ram")) || name == "gc_mem.tmp"
                });
            if !is_arena_file {
                continue;
            }

            let Some((start, end)) = parts[0].split_once('-') else {
                continue;
            };
            if let (Ok(start), Ok(end)) =
                (u64::from_str_radix(start, 16), u64::from_str_radix(end, 16))
            {
                regions.push((start, end));
            }
        }

        regions
    }
}

#[cfg(windows)]
mod platform_mem {
    use std::ffi::c_void;
    use std::io;
    use std::path::Path;

    use sysinfo::Pid;
    use windows_sys::Win32::Foundation::{CloseHandle, HANDLE, INVALID_HANDLE_VALUE};
    use windows_sys::Win32::System::Diagnostics::Debug::{ReadProcessMemory, WriteProcessMemory};
    use windows_sys::Win32::System::Diagnostics::ToolHelp::{
        CreateToolhelp32Snapshot, MODULEENTRY32W, Module32FirstW, TH32CS_SNAPMODULE,
        TH32CS_SNAPMODULE32,
    };
    use windows_sys::Win32::System::Memory::{
        MEM_COMMIT, MEM_MAPPED, MEMORY_BASIC_INFORMATION, VirtualQueryEx,
    };
    use windows_sys::Win32::System::Threading::{
        OpenProcess, PROCESS_QUERY_INFORMATION, PROCESS_VM_OPERATION, PROCESS_VM_READ,
        PROCESS_VM_WRITE,
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
                    PROCESS_VM_READ
                        | PROCESS_VM_WRITE
                        | PROCESS_VM_OPERATION
                        | PROCESS_QUERY_INFORMATION,
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

    // Collect regions that could belong to PPSSPP's emulated-memory arena. PPSSPP allocates the
    // arena as an anonymous pagefile-backed file mapping, so there's no name to search for;
    // instead we gather every committed mapped-file region and let the caller pick out the arena
    // by its distinctive layout.
    pub fn psp_arena_candidates(_pid: Pid, memory: &MemoryHandle) -> Vec<(u64, u64)> {
        let mut regions = Vec::new();
        let mut address = 0u64;
        loop {
            let mut info: MEMORY_BASIC_INFORMATION = unsafe { std::mem::zeroed() };
            // SAFETY: `info` is a valid, writable MEMORY_BASIC_INFORMATION.
            let len = unsafe {
                VirtualQueryEx(
                    memory.process,
                    address as *const c_void,
                    &mut info,
                    size_of::<MEMORY_BASIC_INFORMATION>(),
                )
            };
            if len == 0 {
                break;
            }

            let start = info.BaseAddress as u64;
            let size = info.RegionSize as u64;
            if info.State == MEM_COMMIT && info.Type == MEM_MAPPED {
                regions.push((start, start + size));
            }

            address = match start.checked_add(size) {
                Some(next) if next > address => next,
                _ => break,
            };
        }

        regions
    }
}

use platform_mem::{MemoryHandle, find_module_base, psp_arena_candidates};

// Locate EEmem in the symbol table (Linux debug builds) and return its address.
fn find_symbol_address(file: &object::File) -> Option<u64> {
    file.symbols()
        .find(|symbol| symbol.name() == Ok(EE_MEM_SYMBOL))
        .map(|symbol| symbol.address())
}

// Locate EEmem in the export table (Windows builds) and return its address.
fn find_export_address(file: &object::File) -> Option<u64> {
    file.exports()
        .ok()?
        .into_iter()
        .find(|export| export.name() == EE_MEM_SYMBOL.as_bytes())
        .map(|export| export.address())
}

// Pick out PPSSPP's main RAM view from candidate regions of the emulator's address space.
// Returns the host address corresponding to PSP address 0x08000000 and the RAM size. The RAM
// view is identified by its layout: it's the lowest-addressed region of at least 31MB that has
// an uncached mirror 0x40000000 above it and the VRAM views 0x04000000 below it.
fn find_psp_ram(mut regions: Vec<(u64, u64)>) -> Option<(u64, usize)> {
    regions.sort_unstable();

    // Coalesce adjacent regions: RAM is mapped in up-to-31MB pieces the OS may report
    // separately, and the four consecutive 2MB VRAM views always report separately.
    let mut merged: Vec<(u64, u64)> = Vec::new();
    for (start, end) in regions {
        match merged.last_mut() {
            Some((_, last_end)) if *last_end == start => *last_end = end,
            _ => merged.push((start, end)),
        }
    }

    let contains = |addr: u64| {
        merged
            .iter()
            .any(|&(start, end)| (start..end).contains(&addr))
    };

    for &(start, end) in &merged {
        if end - start < PSP_RAM_VIEW_MIN_SIZE {
            continue;
        }
        let Some(vram) = start.checked_sub((PSP_RAM_BASE - PSP_VRAM_BASE) as u64) else {
            continue;
        };
        if contains(start + PSP_MIRROR_STRIDE) && contains(vram) {
            let ram_size = ((end - start) as usize).min(PSP_RAM_MAX_SIZE);
            return Some((start, ram_size));
        }
    }

    None
}

/// The console whose emulator we're attached to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Console {
    Ps2,
    Psp,
}

enum Backend {
    /// PCSX2. Addresses are offsets into EE RAM, whose host location we get from the pointer
    /// the emulator's EEmem symbol resolves to.
    Pcsx2 { ee_mem_base: u64 },
    /// PPSSPP. Addresses are PSP virtual addresses; `ram_base` is the host address of the
    /// cached RAM view at PSP address 0x08000000.
    Ppsspp { ram_base: u64, ram_size: usize },
}

pub struct Emulator {
    memory: MemoryHandle,
    backend: Backend,
    pid: Pid,
}

impl Emulator {
    fn try_get_emulator_from_process(pid: Pid, process: &Process) -> Option<Self> {
        let exe_path = process.exe()?;
        let lc_exe_name = exe_path.file_name()?.to_string_lossy().to_lowercase();

        if lc_exe_name.starts_with(PCSX2_EXE_PREFIX) {
            Self::attach_pcsx2(pid, exe_path)
        } else if lc_exe_name.starts_with(PPSSPP_EXE_PREFIX) {
            Self::attach_ppsspp(pid)
        } else {
            None
        }
    }

    fn attach_pcsx2(pid: Pid, exe_path: &std::path::Path) -> Option<Self> {
        // search for EEmem
        // TODO: error handling
        let data = fs::read(exe_path).ok()?;
        let file = object::File::parse(&*data).ok()?;
        // `relative_address_base` is the image base for PE and 0 for ELF, so subtracting it
        // converts the resolved address into an offset relative to the module's load address.
        let relative_base = file.relative_address_base();

        // Linux builds of PCSX2 expose EEmem as a debug symbol, but Windows builds export it
        // instead, so check the export table as a fallback when it isn't in the symbol table.
        let ee_mem_addr = find_symbol_address(&file).or_else(|| find_export_address(&file))?;

        // we've found the PCSX2 process; now find the start of EE memory
        let module_base = find_module_base(pid, exe_path)?;
        let ee_mem_ptr = ee_mem_addr - relative_base + module_base;

        let memory = MemoryHandle::open(pid).ok()?;
        let mut buf = [0u8; 8];
        memory.read_at(&mut buf, ee_mem_ptr).ok()?;
        let ee_mem_base = u64::from_le_bytes(buf);
        Some(Self {
            memory,
            backend: Backend::Pcsx2 { ee_mem_base },
            pid,
        })
    }

    fn attach_ppsspp(pid: Pid) -> Option<Self> {
        let memory = MemoryHandle::open(pid).ok()?;
        // PPSSPP has no symbol we can resolve to locate emulated memory, but its memory arena
        // has a distinctive enough layout to identify directly in the process's mappings. The
        // arena isn't allocated until a game is loaded, so this fails (and we keep searching)
        // while PPSSPP is sitting in its menus.
        let (ram_base, ram_size) = find_psp_ram(psp_arena_candidates(pid, &memory))?;
        Some(Self {
            memory,
            backend: Backend::Ppsspp { ram_base, ram_size },
            pid,
        })
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

    pub const fn console(&self) -> Console {
        match self.backend {
            Backend::Pcsx2 { .. } => Console::Ps2,
            Backend::Ppsspp { .. } => Console::Psp,
        }
    }

    pub const fn name(&self) -> &'static str {
        match self.backend {
            Backend::Pcsx2 { .. } => "PCSX2",
            Backend::Ppsspp { .. } => "PPSSPP",
        }
    }

    /// Whether `size` bytes at `address` fall entirely within the region where game data can
    /// live. Used to sanity-check pointers read from game memory before following them.
    pub fn is_address_valid(&self, address: usize, size: usize) -> bool {
        match self.backend {
            Backend::Pcsx2 { .. } => address >= EE_MIN_ADDRESS && address + size <= EE_MEM_SIZE,
            Backend::Ppsspp { ram_size, .. } => {
                let masked = address & PSP_ADDRESS_MASK;
                masked >= PSP_USER_MIN_ADDRESS && masked + size <= PSP_RAM_BASE + ram_size
            }
        }
    }

    // Bounds-check a game address range and translate it to a host address.
    fn translate(&self, address: usize, size: usize) -> Result<u64> {
        let out_of_range = |msg| Err(std::io::Error::new(ErrorKind::UnexpectedEof, msg).into());
        match self.backend {
            Backend::Pcsx2 { ee_mem_base } => {
                if address.saturating_add(size) > EE_MEM_SIZE {
                    return out_of_range("address out of range of EE memory");
                }
                Ok(ee_mem_base + address as u64)
            }
            Backend::Ppsspp { ram_base, ram_size } => {
                let masked = address & PSP_ADDRESS_MASK;
                match masked.checked_sub(PSP_RAM_BASE) {
                    Some(offset) if offset.saturating_add(size) <= ram_size => {
                        Ok(ram_base + offset as u64)
                    }
                    _ => out_of_range("address out of range of PSP RAM"),
                }
            }
        }
    }

    pub fn read_memory(&self, address: usize, size: usize) -> Result<Vec<u8>> {
        let host_address = self.translate(address, size)?;
        let mut buf = vec![0u8; size];
        self.memory.read_at(&mut buf, host_address)?;
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
        let host_address = self.translate(address, data.len())?;
        self.memory.write_at(data, host_address)?;
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

#[cfg(test)]
mod tests {
    use super::*;

    const BASE: u64 = 0x2300000000;

    // The full set of arena views PPSSPP maps for 32MB of RAM, before any OS coalescing:
    // scratchpad + uncached mirror, 4 cached + 4 uncached VRAM views, and 31MB + 1MB RAM
    // pieces at the cached, uncached, and two kernel mirrors.
    fn ppsspp_regions() -> Vec<(u64, u64)> {
        let mut regions = vec![
            (BASE + 0x00010000, BASE + 0x00014000),
            (BASE + 0x40010000, BASE + 0x40014000),
        ];
        for i in 0..4 {
            let vram = BASE + 0x04000000 + i * 0x200000;
            regions.push((vram, vram + 0x200000));
            let uncached = BASE + 0x44000000 + i * 0x200000;
            regions.push((uncached, uncached + 0x200000));
        }
        for mirror in [0x08000000u64, 0x48000000, 0x88000000, 0xC8000000] {
            regions.push((BASE + mirror, BASE + mirror + 0x1F00000));
            regions.push((BASE + mirror + 0x1F00000, BASE + mirror + 0x2000000));
        }
        regions
    }

    #[test]
    fn finds_ram_in_split_views() {
        let result = find_psp_ram(ppsspp_regions());
        assert_eq!(result, Some((BASE + 0x08000000, 0x2000000)));
    }

    #[test]
    fn finds_ram_in_coalesced_views() {
        let regions = vec![
            (BASE + 0x00010000, BASE + 0x00014000),
            (BASE + 0x04000000, BASE + 0x04800000),
            (BASE + 0x08000000, BASE + 0x0A000000),
            (BASE + 0x40010000, BASE + 0x40014000),
            (BASE + 0x44000000, BASE + 0x44800000),
            (BASE + 0x48000000, BASE + 0x4A000000),
            (BASE + 0x88000000, BASE + 0x8A000000),
            (BASE + 0xC8000000, BASE + 0xCA000000),
        ];
        let result = find_psp_ram(regions);
        assert_eq!(result, Some((BASE + 0x08000000, 0x2000000)));
    }

    #[test]
    fn rejects_large_mapping_without_arena_layout() {
        // a large mapped file (e.g. a memory-mapped ISO) with no mirror or VRAM views
        let regions = vec![(BASE, BASE + 0x30000000)];
        assert_eq!(find_psp_ram(regions), None);
    }

    #[test]
    fn rejects_empty() {
        assert_eq!(find_psp_ram(Vec::new()), None);
    }
}
