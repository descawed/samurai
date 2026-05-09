use std::path::Path;

use anyhow::{anyhow, Result};

use crate::module::ModuleArchive;
use crate::Readable;

pub fn unpack_modules(archive_path: &Path, extract_path: &Path) -> Result<()> {
    if !extract_path.is_dir() {
        return Err(anyhow!("Extract path must be a directory"));
    }
    
    let archive = ModuleArchive::load(archive_path)?;
    for (i, module) in archive.modules().iter().enumerate() {
        let output_path = extract_path.join(i.to_string());
        std::fs::write(&output_path, module)?;
    }
    
    Ok(())
}

pub fn pack_modules<T, I>(archive_path: &Path, alignment: u32, import_paths: I) -> Result<()>
where T: AsRef<Path>, I: Iterator<Item = T>
{
    let mut archive = ModuleArchive::new(alignment);
    for import_path in import_paths {
        let data = std::fs::read(import_path)?;
        archive.add_module(data);   
    }
    
    archive.write(std::fs::File::create(archive_path)?)
}