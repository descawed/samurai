use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader, Cursor, ErrorKind};
use std::ops::Deref;
use std::os::unix::fs::FileExt;

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

pub struct Emulator {
    memory: File,
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
        for symbol in file.symbols() {
            if !matches!(symbol.name().map(|name| name == EE_MEM_SYMBOL), Ok(true)) {
                continue;
            }

            // we've found the PCSX2 process; now find the start of EE memory
            let exe_path = exe_path.to_string_lossy();
            let mut ee_mem_ptr = symbol.address();
            let memory_map = BufReader::new(File::open(format!("/proc/{}/maps", pid)).ok()?);
            for line in memory_map.lines() {
                let line = line.ok()?;
                let parts: Vec<_> = line.split_whitespace().collect();
                if parts.len() != 6 {
                    continue;
                }

                if parts[5] == exe_path {
                    let base_address = u64::from_str_radix(parts[0].split('-').next()?, 16).ok()?;
                    ee_mem_ptr += base_address;
                    break;
                }
            }

            let memory = File::open(format!("/proc/{}/mem", pid)).unwrap();
            let mut buf = [0u8; 8];
            memory.read_exact_at(&mut buf, ee_mem_ptr).unwrap();
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
            .read_exact_at(&mut buf, (self.ee_mem_base + address) as u64)?;
        Ok(buf)
    }

    pub fn read<'a, T: BinRead<Args<'a> = ()>>(&self, address: usize, size: usize) -> Result<T> {
        let data = self.read_memory(address, size)?;
        let value = Cursor::new(data).read_le()?;
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
            .write_all_at(&data, (self.ee_mem_base + address) as u64)?;
        Ok(())
    }

    pub fn write<T: for<'a> BinWrite<Args<'a> = ()>>(
        &self,
        address: usize,
        value: &T,
    ) -> Result<()> {
        let mut buf = Cursor::new(Vec::new());
        value.write_le(&mut buf)?;
        self.write_memory(address, &buf.into_inner())?;
        Ok(())
    }
}
