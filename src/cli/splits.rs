use std::path::Path;

use anyhow::{bail, Result};

use crate::autosplitter::routes::ROUTES;

pub fn create_splits(dir: &Path, skip_existing: bool) -> Result<()> {
    if !dir.exists() {
        std::fs::create_dir_all(dir)?;
    } else if !dir.is_dir() {
        bail!("{} is not a directory", dir.display());
    }
    
    for route in ROUTES {
        let filename = format!("{}.lss", route.splits_name());
        let splits_path = dir.join(&filename);
        if splits_path.exists() && skip_existing {
            log::info!("Skipping existing splits file: {}", splits_path.display());
            continue;
        }
        log::info!("Generating splits file: {}", splits_path.display());
        let splits = route.to_splits()?;
        std::fs::write(splits_path, splits)?;
    }
    
    Ok(())
}