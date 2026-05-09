use std::io::{Read, Seek, SeekFrom, Write};

use anyhow::Result;
use binrw::{binrw, BinReaderExt, BinWriterExt};

use crate::{Readable, Validated};

pub const DEFAULT_ALIGNMENT: u32 = 0x40;

#[binrw]
#[derive(Debug, Clone)]
struct ModuleHeader {
    #[bw(calc = module_sizes.len() as u32)]
    num_modules: u32,
    // header_size and alignment could actually be backwards; I've only ever seen them have the
    // same value
    header_size: u32,
    alignment: u32,
    unknown: u32,
    #[br(count = num_modules)]
    #[brw(pad_size_to = header_size - 16)]
    module_sizes: Vec<u32>,
}

impl ModuleHeader {
    const fn new(alignment: u32, module_sizes: Vec<u32>) -> Self {
        let header_size = ((16 + module_sizes.len() * 4) as u32).next_multiple_of(alignment);
        Self {
            header_size,
            alignment,
            unknown: 0,
            module_sizes,
        }
    }
}

#[derive(Debug)]
pub struct ModuleArchive {
    alignment: u32,
    modules: Vec<Vec<u8>>,
}

impl ModuleArchive {
    pub fn new(alignment: u32) -> Self {
        Self {
            alignment,
            modules: vec![],
        }
    }

    pub fn add_module(&mut self, module: Vec<u8>) {
        self.modules.push(module);
    }

    pub fn set_modules(&mut self, modules: Vec<Vec<u8>>) {
        self.modules = modules;
    }

    pub fn modules(&self) -> &[Vec<u8>] {
        &self.modules
    }

    pub fn write<F: Write + Seek>(&self, mut f: F) -> Result<()> {
        let module_sizes = self.modules.iter().map(|m| m.len() as u32).collect::<Vec<_>>();
        let header = ModuleHeader::new(self.alignment, module_sizes);

        f.write_le(&header)?;

        let alignment = self.alignment as usize;
        for module in &self.modules {
            f.write_all(module)?;
            let padding = alignment - (module.len() % alignment);
            if padding > 0 {
                f.write_all(&vec![0u8; padding])?;
            }
        }

        Ok(())
    }
}

impl Readable for ModuleArchive {
    fn read<F: Read + Seek>(mut source: F) -> Result<Validated<Self>> {
        let header = source.read_le::<ModuleHeader>()?;
        let mut warnings = vec![];

        let alignment = header.alignment;
        if !alignment.is_power_of_two() {
            warnings.push("Alignment is not a power of two".to_string());
        }

        let mut modules = Vec::with_capacity(header.module_sizes.len());

        for module_size in header.module_sizes {
            let mut module = vec![0u8; module_size as usize];
            source.read_exact(&mut module)?;
            modules.push(module);

            let padding = (alignment - (module_size % alignment)) as i64;
            if padding > 0 {
                source.seek(SeekFrom::Current(padding))?;
            }
        }

        Ok(Validated {
            object: Self {
                alignment,
                modules,
            },
            warnings,
        })
    }
}