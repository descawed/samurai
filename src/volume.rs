use std::collections::HashMap;
use std::io::{Read, Seek, SeekFrom, Write};

use anyhow::{anyhow, Result};
use binrw::{BinRead, binrw, BinWrite, BinWriterExt, NullString};

/// The default maximum number of objects a volume can hold.
pub const DEFAULT_MAX_OBJECTS: u32 = 4000;
const DESCRIPTOR_SIZE: u32 = 24;
const HEADER_SIZE: u32 = 20;

/// Compute the hash of the name of an object in the volume.
///
/// The hash must uniquely identify the object within the volume. Prior to hashing, the name will
/// be converted to uppercase and forward slashes will be replaced with backslashes.
fn hash_name(name: &[u8]) -> u32 {
    name.iter().map(|c| if *c == b'/' { b'\\' } else { c.to_ascii_uppercase() } as u32).fold(0, |acc, c| acc.overflowing_mul(0x13).0.overflowing_add(c).0)
}

/// Round up to the next multiple of 256 (low 8 bits zero)
const fn round8(value: u32) -> u32 {
    (value + 0xFF) & !0xFF
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
    objects: HashMap<String, Vec<u8>>,
}

impl Volume {
    /// Create a new, empty volume that can hold up to the given number of objects
    pub fn new(max_objects: u32) -> Self {
        Self {
            max_objects,
            objects: HashMap::new(),
        }
    }

    /// Read a volume from a binary data stream
    pub fn read<F: Read + Seek>(mut source: F) -> Result<Self> {
        let header = VolumeHeader::read(&mut source)?;
        let mut objects = HashMap::with_capacity(header.descriptors.len());
        for descriptor in &header.descriptors {
            source.seek(SeekFrom::Start(
                (header.header_size + descriptor.start) as u64,
            ))?;
            let mut data = vec![0u8; descriptor.size as usize];
            source.read_exact(&mut data)?;
            let name = NullString::read(&mut source)?;
            objects.insert(name.to_string(), data);
            // TODO: remove once debugging complete
            if descriptor.unknown != 0 {
                println!(
                    "{} (hash {:08X}) has non-zero unknown value {}",
                    name, descriptor.hash, descriptor.unknown
                );
            }
        }

        Ok(Self {
            max_objects: header.max_objects,
            objects,
        })
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

        let mut hashes = HashMap::with_capacity(self.objects.len());
        let mut header = VolumeHeader {
            max_objects: self.max_objects,
            header_size: round8(self.max_objects * DESCRIPTOR_SIZE + HEADER_SIZE),
            file_size: 0,
            descriptors: Vec::with_capacity(self.objects.len()),
        };

        sink.seek(SeekFrom::Start(header.header_size as u64))?;
        let mut start = 0usize;
        for (name, data) in &self.objects {
            let hash = hash_name(name.as_bytes());
            if hashes.contains_key(&hash) {
                return Err(anyhow!(
                    "Hash collision: hash {:08X}, first name {}, second name {}",
                    hash,
                    hashes[&hash],
                    name
                ));
            }
            hashes.insert(hash, name.clone());

            sink.write(data)?;
            sink.write(name.as_bytes())?;
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

            start = round8(object_end as u32) as usize;
            let padding = start - object_end;
            sink.seek(SeekFrom::Current(padding as i64))?;
        }

        // go back and finish up the header
        header.descriptors.sort_by_key(|d| d.hash); // descriptors must be sorted by hash because the game finds entries by binary search
        let file_size = sink.seek(SeekFrom::Current(0))?;
        header.file_size = (file_size & !0xFFF) as u32; // FIXME: is this right?
        sink.seek(SeekFrom::Start(0))?;
        header.write(&mut sink)?;

        Ok(())
    }

    /// Get the data for the object with the given name if the object exists.
    pub fn get(&self, name: &str) -> Option<&[u8]> {
        self.objects.get(name).map(Vec::as_slice)
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
    pub fn add(&mut self, name: String, data: Vec<u8>) {
        self.objects.insert(name, data);
    }

    /// Remove the object with the given name from the volume.
    pub fn remove(&mut self, name: &str) {
        self.objects.remove(name);
    }

    /// Does this volume contain an object with the given name?
    pub fn has(&self, name: &str) -> bool {
        self.objects.contains_key(name)
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
        assert_eq!(round8(4000 * DESCRIPTOR_SIZE + HEADER_SIZE), 0x17800);
    }
}
