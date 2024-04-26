use std::collections::HashMap;
use std::io::{Read, Seek, SeekFrom, Write};

use anyhow::{anyhow, Result};
use binrw::{binrw, BinRead, BinWrite, BinWriterExt, NullString};
use ordered_hash_map::OrderedHashMap;

use super::{Readable, Validated};

/// The default maximum number of objects a volume can hold.
pub const DEFAULT_MAX_OBJECTS: u32 = 4000;
const DESCRIPTOR_SIZE: u32 = 24;
const HEADER_SIZE: u32 = 20;

/// Compute the hash of the name of an object in the volume.
///
/// The hash must uniquely identify the object within the volume. Prior to hashing, the name will
/// be converted to uppercase and forward slashes will be replaced with backslashes.
pub fn hash_name(name: &[u8]) -> u32 {
    name.iter().map(|c| if *c == b'/' { b'\\' } else { c.to_ascii_uppercase() } as u32).fold(0, |acc, c| acc.overflowing_mul(0x13).0.overflowing_add(c).0)
}

/// Round up to the next sector (multiple of 2048)
const fn round_sector(value: u32) -> u32 {
    (value + 0x7FF) & !0x7FF
}

#[binrw]
#[brw(big)]
struct ObjectDescriptor {
    hash: u32,
    start: u32,
    size: u32,
    unknown: u32,
    end: u32,
    name_size: u32,
}

#[binrw]
#[brw(big, magic = 0xFADEBABEu32)]
struct VolumeHeader {
    max_objects: u32, // this is a guess, but it lines up if we assume the header size is always rounded up to a multiple of 0x100
    #[bw(calc = descriptors.len() as u32)]
    num_objects: u32,
    header_size: u32,
    file_size: u32, // this isn't the exact file size. the difference is close to the header_size, but a little less.
    #[br(count = num_objects)]
    descriptors: Vec<ObjectDescriptor>,
}

/// An archive of the game's files (volume.dat).
///
/// This struct keeps the entire archive contents in memory. This isn't super efficient in terms of resources,
/// but it significantly simplifies the design.
#[derive(Debug)]
pub struct Volume {
    max_objects: u32,
    objects: OrderedHashMap<String, Vec<u8>>,
    hashes: HashMap<u32, String>,
}

impl Volume {
    /// Create a new, empty volume that can hold up to the given number of objects
    ///
    /// # Arguments
    ///
    /// * `max_objects` - The maximum number of objects to reserve space for in the volume's header.
    ///
    /// # Returns
    ///
    /// An empty volume
    pub fn new(max_objects: u32) -> Self {
        Self {
            max_objects,
            objects: OrderedHashMap::new(),
            hashes: HashMap::new(),
        }
    }

    /// Get the current maximum number of objects for this volume
    pub fn max_objects(&self) -> u32 {
        self.max_objects
    }

    /// Set the maximum number of objects for this volume
    ///
    /// # Errors
    ///
    /// Returns an error of the number of objects currently in the volume exceeds the requested maximum.
    pub fn set_max_objects(&mut self, max_objects: u32) -> Result<()> {
        if self.objects.len() > max_objects as usize {
            return Err(anyhow!(
                "Volume already contains more than {} objects",
                max_objects
            ));
        }
        self.max_objects = max_objects;
        Ok(())
    }

    /// Write this volume to a binary data stream
    pub fn write<F: Write + Seek>(&self, mut sink: F) -> Result<()> {
        if self.objects.len() > self.max_objects as usize {
            return Err(anyhow!(
                "Too many objects in the volume: max {}, actual {}",
                self.max_objects,
                self.objects.len()
            ));
        }

        let header_size = self.max_objects * DESCRIPTOR_SIZE + HEADER_SIZE;
        let mut header = VolumeHeader {
            max_objects: self.max_objects,
            header_size: round_sector(header_size),
            file_size: 0,
            descriptors: Vec::with_capacity(self.objects.len()),
        };

        sink.seek(SeekFrom::Start(header.header_size as u64))?;
        let mut start = 0usize;
        for (name, data) in &self.objects {
            let hash = hash_name(name.as_bytes());
            sink.write_all(data)?;
            sink.write_all(name.as_bytes())?;
            sink.write_be(&0u8)?;
            let end = start + data.len();
            let object_end = end + name.len() + 1;
            header.descriptors.push(ObjectDescriptor {
                hash,
                start: start as u32,
                size: data.len() as u32,
                unknown: 0, // never seen any other value for this
                end: end as u32,
                name_size: name.len() as u32 + 1, // +1 for null byte
            });

            start = round_sector(object_end as u32) as usize;
            let padding = start - object_end;
            sink.seek(SeekFrom::Current(padding as i64))?;
        }

        // go back and finish up the header
        header.descriptors.sort_by_key(|d| d.hash); // descriptors must be sorted by hash because the game finds entries by binary search
        let file_size = sink.stream_position()? as u32 - header_size;
        header.file_size = file_size & !0x7FF; // this seems to round down to the nearest sector instead of up
        sink.seek(SeekFrom::Start(0))?;
        header.write(&mut sink)?;

        Ok(())
    }

    /// Get the data for the object with the given name if the object exists.
    pub fn get(&self, name: &str) -> Option<&[u8]> {
        self.objects.get(name).map(Vec::as_slice)
    }

    /// Get the data for the object with the given hash if the object exists.
    pub fn get_by_hash(&self, hash: u32) -> Option<&[u8]> {
        self.hashes
            .get(&hash)
            .and_then(|name| self.objects.get(name))
            .map(Vec::as_slice)
    }

    /// Iterate over the objects in the volume along with their names
    pub fn iter(&self) -> impl Iterator<Item = (&str, &[u8])> {
        self.objects.iter().map(|(s, o)| (s.as_str(), o.as_slice()))
    }

    /// Iterate mutably over the objects in the volume along with their names
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&str, &mut Vec<u8>)> {
        self.objects.iter_mut().map(|(s, o)| (s.as_str(), o))
    }

    /// Add or replace an object in the volume with the given name.
    pub fn add(&mut self, name: String, data: Vec<u8>) -> Result<u32> {
        if self.objects.len() >= self.max_objects as usize {
            return Err(anyhow!(
                "The volume is full (maximum number of objects {})",
                self.max_objects
            ));
        }

        let hash = hash_name(name.as_bytes());
        if let Some(other_name) = self.hashes.get(&hash) {
            return Err(anyhow!(
                "Hash collision: hash {:08X} already used by {}",
                hash,
                other_name
            ));
        }
        self.objects.insert(name.clone(), data);
        self.hashes.insert(hash, name);
        Ok(hash)
    }

    /// Remove the object with the given name from the volume.
    ///
    /// # Returns
    ///
    /// Whether an object was removed
    pub fn remove(&mut self, name: &str) -> bool {
        let hash = hash_name(name.as_bytes());
        self.hashes.remove(&hash);
        self.objects.remove(name).is_some()
    }

    /// Remove the object with the given hash from the volume
    ///
    /// # Returns
    ///
    /// Whether an object was removed
    pub fn remove_by_hash(&mut self, hash: u32) -> bool {
        if let Some(name) = self.hashes.remove(&hash) {
            self.objects.remove(&name);
            true
        } else {
            false
        }
    }

    /// Does this volume contain an object with the given name?
    pub fn has(&self, name: &str) -> bool {
        self.objects.contains_key(name)
    }

    /// Does this volume contain an object with the given hash?
    pub fn has_hash(&self, hash: u32) -> bool {
        self.hashes.contains_key(&hash)
    }
}

impl Readable for Volume {
    /// Read a volume from a binary data stream while validating its contents
    ///
    /// # Arguments
    ///
    /// * `source` - The binary data stream to read the volume from
    ///
    /// # Returns
    ///
    /// A Validated<Volume> containing the volume and any validation warnings that were encountered.
    fn read<F: Read + Seek>(mut source: F) -> Result<Validated<Self>> {
        let mut warnings = vec![];

        let mut header = VolumeHeader::read(&mut source)?;
        let num_objects = header.descriptors.len();
        if num_objects > header.max_objects as usize {
            warnings.push(format!(
                "Volume contains more than the maximum number of objects: max {}, actual {}",
                header.max_objects, num_objects
            ));
        }

        // the descriptors will be sorted as necessary when writing, so make sure we keep things in
        // the original file order
        header.descriptors.sort_by_key(|d| d.start);
        let mut objects = OrderedHashMap::with_capacity(num_objects);
        let mut hashes = HashMap::with_capacity(num_objects);
        for (i, descriptor) in header.descriptors.iter().enumerate() {
            source.seek(SeekFrom::Start(
                (header.header_size + descriptor.start) as u64,
            ))?;
            let mut data = vec![0u8; descriptor.size as usize];
            source.read_exact(&mut data)?;
            let name = NullString::read(&mut source)?.to_string();

            let hash = hash_name(name.as_bytes());
            if hash != descriptor.hash {
                warnings.push(format!(
                    "{} (index {}) hash looks wrong: expected {:08X}, actual {:08X}",
                    name, i, hash, descriptor.hash
                ));
            }

            if descriptor.unknown != 0 {
                warnings.push(format!(
                    "{} (index {}, hash {:08X}) has non-zero unknown value: {}",
                    name, i, hash, descriptor.unknown
                ));
            }
            objects.insert(name.clone(), data);
            hashes.insert(hash, name);
        }

        Ok(Validated {
            object: Self {
                max_objects: header.max_objects,
                objects,
                hashes,
            },
            warnings,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash() {
        assert_eq!(hash_name(b"chara\\aka.sdp"), 0x5d52482b);
    }

    #[test]
    fn test_round() {
        assert_eq!(round_sector(4000 * DESCRIPTOR_SIZE + HEADER_SIZE), 0x17800);
    }
}
