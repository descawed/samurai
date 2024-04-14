use std::fs::File;
use std::io::BufReader;
use std::path::Path;

use anyhow::Result;

use volume::*;

pub mod script;
pub mod volume;

/// An object whose status has been validated, with any warnings recorded in the warnings member
#[derive(Debug)]
pub struct Validated<T> {
    pub object: T,
    pub warnings: Vec<String>,
}

pub fn load_volume(path: &Path) -> Result<Volume> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    Volume::read(reader)
}
