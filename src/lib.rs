use std::any;
use std::fmt;
use std::fmt::Formatter;
use std::fs::File;
use std::io::{BufReader, Read, Seek};
use std::ops::Deref;
use std::path::Path;

use anyhow::{anyhow, Result};

pub mod script;
pub mod texture;
pub mod volume;

/// A trait for objects that can be read from a binary data stream
pub trait Readable {
    fn read<F: Read + Seek>(source: F) -> Result<Validated<Self>>
    where
        Self: Sized;

    fn load(path: &Path) -> Result<Validated<Self>>
    where
        Self: Sized,
    {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        Self::read(reader)
    }
}

/// An object whose status has been validated, with any warnings recorded in the warnings member
#[derive(Debug)]
pub struct Validated<T: Sized> {
    pub object: T,
    pub warnings: Vec<String>,
}

impl<T: Sized> Validated<T> {
    pub fn valid(object: T) -> Self {
        Self {
            object,
            warnings: vec![],
        }
    }

    pub fn combine<'a, I>(context: I) -> Vec<String>
    where
        T: 'a,
        I: IntoIterator<Item = &'a Validated<T>>, // https://users.rust-lang.org/t/why-do-i-need-higher-ranked-trait-bounds-to-borrow-from-a-generic-intoiter-t/100255
    {
        let mut warnings = vec![];
        for (i, other) in context.into_iter().enumerate() {
            for warning in &other.warnings {
                warnings.push(format!("{} {}: {}", any::type_name::<T>(), i, warning));
            }
        }

        warnings
    }

    pub fn is_valid(&self) -> bool {
        self.warnings.is_empty()
    }

    pub fn some(self) -> Option<T> {
        self.is_valid().then_some(self.object)
    }

    pub fn ok(self) -> Result<T> {
        if self.is_valid() {
            Ok(self.object)
        } else {
            Err(anyhow!(
                "The {} was invalid due to the following errors:\n{}",
                any::type_name::<T>(),
                self.warnings.join("\n")
            ))
        }
    }
}

impl<T: Sized> Deref for Validated<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.object
    }
}

impl<T: fmt::Display + Sized> fmt::Display for Validated<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.object.fmt(f)?;
        if !self.is_valid() {
            write!(f, ". INVALID: {}", self.warnings.join("; "))?;
        }
        Ok(())
    }
}
