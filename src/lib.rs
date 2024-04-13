use std::fs::File;
use std::io::BufReader;
use std::path::Path;

use anyhow::Result;

pub use volume::*;

mod volume;

pub fn load_volume(path: &Path) -> Result<Volume> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    Volume::read(reader)
}
