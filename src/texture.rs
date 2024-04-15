use std::borrow::Cow;
use std::fmt;
use std::fmt::Formatter;
use std::io::{Read, Seek, SeekFrom};
use std::ops::Index;

use crate::{Readable, Validated};
use anyhow::{anyhow, Result};
use binrw::{binrw, BinRead};
use image::{imageops, DynamicImage, RgbaImage};

const fn scale_alpha(alpha: u8) -> u8 {
    if alpha > 128 {
        255
    } else {
        ((alpha as u16 * 255) / 128) as u8
    }
}

#[derive(Debug, Copy, Clone)]
pub enum StackDirection {
    Horizontal,
    Vertical,
}

impl StackDirection {
    pub fn size(&self, width: usize, height: usize, num_cluts: usize) -> (usize, usize) {
        match self {
            StackDirection::Horizontal => (width * num_cluts, height),
            StackDirection::Vertical => (width, height * num_cluts),
        }
    }

    pub fn offset(&self, width: usize, height: usize, i: usize) -> (usize, usize) {
        match self {
            StackDirection::Horizontal => (width * i, 0),
            StackDirection::Vertical => (0, height * i),
        }
    }
}

#[binrw]
#[derive(Debug, Copy, Clone)]
#[brw(little, repr = u16)]
#[repr(u16)]
enum PixelStorageMode {
    PSMCT32 = 0,
    PSMCT24 = 1,
    PSMCT16 = 2,
    PSMCT16S = 10,
    PSMT8 = 19,
    PSMT4 = 20,
    PSMT8H = 27,
    PSMT4HL = 36,
    PSMT4HH = 44,
    PSMZ32 = 48,
    PSMZ24 = 49,
    PSMZ16 = 50,
    PSMZ16S = 58,
}

impl PixelStorageMode {
    pub fn has_transparency(&self) -> bool {
        matches!(
            self,
            PixelStorageMode::PSMCT32 | PixelStorageMode::PSMCT16 | PixelStorageMode::PSMCT16S
        )
    }

    pub fn has_clut(&self) -> bool {
        matches!(
            self,
            PixelStorageMode::PSMT8
                | PixelStorageMode::PSMT4
                | PixelStorageMode::PSMT8H
                | PixelStorageMode::PSMT4HL
                | PixelStorageMode::PSMT4HH
        )
    }

    pub fn num_clut_colors(&self) -> usize {
        match self {
            PixelStorageMode::PSMT8H | PixelStorageMode::PSMT8 => 256,
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH | PixelStorageMode::PSMT4 => 16,
            _ => 0,
        }
    }

    pub fn num_clut_bytes(&self, other: Self) -> usize {
        match (self.has_clut(), other.has_clut()) {
            (true, false) => self.num_clut_colors() * other.pixel_size().unwrap(),
            (false, true) => other.num_clut_colors() * self.pixel_size().unwrap(),
            _ => 0,
        }
    }

    pub fn num_index_bytes(&self, width: usize, height: usize) -> usize {
        let area = width * height;
        match self {
            PixelStorageMode::PSMT8 => area,
            PixelStorageMode::PSMT4 => area.div_ceil(2),
            // FIXME: is it right that we only get one index per word with the PSMT4 formats?
            PixelStorageMode::PSMT8H | PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH => {
                area * 4
            }
            _ => 0,
        }
    }

    pub fn num_pixel_bytes(&self, width: usize, height: usize) -> usize {
        self.pixel_size().map_or(0, |s| s * width * height)
    }

    pub fn num_image_bytes(&self, width: usize, height: usize) -> usize {
        if self.has_clut() {
            self.num_index_bytes(width, height)
        } else {
            self.num_pixel_bytes(width, height)
        }
    }

    pub fn pixel_size(&self) -> Option<usize> {
        match self {
            PixelStorageMode::PSMCT32 => Some(4),
            PixelStorageMode::PSMCT24 => Some(3),
            PixelStorageMode::PSMCT16 | PixelStorageMode::PSMCT16S => Some(2),
            _ => None,
        }
    }

    pub fn read_pixels(&self, data: &[u8]) -> Result<Vec<u8>> {
        match self {
            PixelStorageMode::PSMCT32 => Ok(data
                .chunks_exact(4)
                .flat_map(|p| [p[0], p[1], p[2], scale_alpha(p[3])])
                .collect()),
            PixelStorageMode::PSMCT24 => Ok(data
                .chunks_exact(4)
                .flat_map(|p| [p[0], p[1], p[2], 255])
                .collect()),
            PixelStorageMode::PSMCT16 => Ok(data
                .chunks_exact(2)
                .map(|p| u16::from_le_bytes([p[0], p[1]]))
                .flat_map(|p| {
                    [
                        (p & 0x1f) as u8,
                        ((p >> 5) & 0x1f) as u8,
                        ((p >> 10) & 0x1f) as u8,
                        if p & 0x8000 != 0 { 255 } else { 0 },
                    ]
                })
                .collect()),
            _ if self.has_clut() => Err(anyhow!(
                "Pixel storage mode {:?} is invalid for pixels",
                self
            )),
            _ => Err(anyhow!("Pixel storage mode {:?} is unsupported", self)),
        }
    }

    pub fn read_indexes(&self, data: &[u8]) -> Result<Vec<usize>> {
        let iter = data.iter();
        match self {
            PixelStorageMode::PSMT8 => Ok(iter.map(|b| *b as usize).collect()),
            PixelStorageMode::PSMT8H => Ok(iter.step_by(4).map(|b| *b as usize).collect()),
            PixelStorageMode::PSMT4 => Ok(iter
                .flat_map(|b| [(*b & 0xf) as usize, (*b >> 4) as usize])
                .collect()),
            PixelStorageMode::PSMT4HL => Ok(iter.step_by(4).map(|b| (*b & 0xf) as usize).collect()),
            PixelStorageMode::PSMT4HH => Ok(iter.step_by(4).map(|b| (*b >> 4) as usize).collect()),
            _ => Err(anyhow!(
                "Pixel storage mode {:?} is invalid for indexes",
                self
            )),
        }
    }
}

#[binrw]
#[derive(Debug)]
#[brw(little)]
struct ImageDescriptor {
    pub unknown00: u16,
    pub pixel_type: PixelStorageMode,
    pub clut_pixel_type: PixelStorageMode, // this is a guess as I've only ever seen zero
    pub unknown06: u16,
    pub unknown08: u16,
    pub unknown0a: u16,
    pub unknown0c: u16,
    pub unknown0e: u16,
    pub width: u16,
    pub height: u16,
    pub image_block_length: u32,
    pub image_block_offset: u32,
    pub num_cluts: u16,
    pub unknown1a: u16,
    pub clut_block_length: u32,
    pub clut_block_offset: u32,
    pub header_count: u16,
    pub unknown2a: u16,
    pub unknown2c: u32,
}

impl ImageDescriptor {
    pub fn calc_clut_block_length(&self) -> usize {
        self.num_cluts as usize * self.pixel_type.num_clut_bytes(self.clut_pixel_type)
    }

    pub fn calc_image_block_length(&self) -> usize {
        self.pixel_type
            .num_image_bytes(self.width as usize, self.height as usize)
    }

    pub fn has_transparency(&self) -> bool {
        self.pixel_type.has_transparency()
            || (self.pixel_type.has_clut() && self.clut_pixel_type.has_transparency())
    }

    pub fn has_clut(&self) -> bool {
        self.pixel_type.has_clut()
    }

    pub fn index_type(&self) -> Option<PixelStorageMode> {
        self.pixel_type.has_clut().then_some(self.pixel_type)
    }

    pub fn pixel_type(&self) -> PixelStorageMode {
        if self.pixel_type.has_clut() {
            self.clut_pixel_type
        } else {
            self.pixel_type
        }
    }
}

#[derive(Debug)]
pub enum ImageData {
    Indexes(Vec<usize>),
    Pixels(Vec<u8>),
}

impl ImageData {
    pub fn get_pixels(&self, clut: Option<&[[u8; 4]]>) -> Cow<'_, Vec<u8>> {
        match self {
            ImageData::Indexes(indexes) => {
                let clut = clut.unwrap();
                Cow::Owned(indexes.iter().flat_map(|i| clut[*i]).collect())
            }
            ImageData::Pixels(pixels) => Cow::Borrowed(pixels),
        }
    }
}

#[derive(Debug)]
pub struct PictureImage {
    descriptor: ImageDescriptor,
    cluts: Vec<Vec<[u8; 4]>>,
    image: ImageData,
}

impl PictureImage {
    fn decode(descriptor: ImageDescriptor, clut: &[u8], image: &[u8]) -> Validated<Self> {
        let mut warnings = vec![];

        let expected_image_block_length = descriptor.calc_image_block_length();
        if image.len() < expected_image_block_length {
            warnings.push(format!(
                "Image buffer is too small; expected at least {} bytes, got {} bytes",
                expected_image_block_length,
                image.len()
            ));
        }

        let num_cluts = descriptor.num_cluts as usize;
        let mut cluts = Vec::with_capacity(num_cluts);
        let image_data = if descriptor.has_clut() {
            let clut_pixels = match descriptor.clut_pixel_type.read_pixels(clut) {
                Ok(result) => result,
                Err(e) => {
                    warnings.push(format!("Error reading CLUT: {}", e));
                    vec![]
                }
            };
            // if there's more data in the buffer than we need to get the expected number of CLUTs,
            // just ignore it
            cluts.extend(
                clut_pixels
                    .chunks_exact(descriptor.pixel_type.num_clut_colors() * 4)
                    .take(num_cluts)
                    .map(|c| {
                        c.chunks_exact(4)
                            .map(|p| [p[0], p[1], p[2], p[3]])
                            .collect()
                    }),
            );
            if cluts.len() < num_cluts {
                warnings.push(format!(
                    "Expected {} CLUTs but only found {}",
                    num_cluts,
                    cluts.len()
                ));
            }

            ImageData::Indexes(match descriptor.pixel_type.read_indexes(image) {
                Ok(indexes) => indexes,
                Err(e) => {
                    warnings.push(format!("Error reading indexes: {}", e));
                    vec![]
                }
            })
        } else {
            ImageData::Pixels(match descriptor.pixel_type.read_pixels(image) {
                Ok(pixels) => pixels,
                Err(e) => {
                    warnings.push(format!("Error reading pixels: {}", e));
                    vec![]
                }
            })
        };

        Validated {
            object: Self {
                descriptor,
                cluts,
                image: image_data,
            },
            warnings,
        }
    }

    pub fn has_transparency(&self) -> bool {
        self.descriptor.has_transparency()
    }

    pub fn num_cluts(&self) -> usize {
        self.cluts.len()
    }

    pub fn to_image_all_cluts(&self, stack: StackDirection) -> DynamicImage {
        let num_cluts = self.cluts.len();
        if num_cluts == 0 {
            return self.to_image();
        }

        let base_width = self.descriptor.width as usize;
        let base_height = self.descriptor.height as usize;
        let (width, height) = stack.size(base_width, base_height, num_cluts);
        let mut image = DynamicImage::new_rgba8(width as u32, height as u32);
        for i in 0..num_cluts {
            let clut_image = self.to_image_with_clut(i);
            let (x, y) = stack.offset(base_width, base_height, i);
            imageops::overlay(&mut image, &clut_image, x as i64, y as i64);
        }

        image
    }

    pub fn to_image_with_clut(&self, clut_index: usize) -> DynamicImage {
        let clut = self.cluts.get(clut_index).map(Vec::as_slice);
        let pixels = self.image.get_pixels(clut);
        DynamicImage::ImageRgba8(
            RgbaImage::from_raw(
                self.descriptor.width as u32,
                self.descriptor.height as u32,
                pixels.into_owned(),
            )
            .unwrap(),
        )
    }

    pub fn to_image(&self) -> DynamicImage {
        self.to_image_with_clut(0)
    }
}

impl fmt::Display for PictureImage {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(index_type) = self.descriptor.index_type() {
            write!(f, "Index type {:?}, ", index_type)?;
        }

        write!(
            f,
            "Pixel type {:?}, {}x{}, {} CLUTs",
            self.descriptor.pixel_type(),
            self.descriptor.width,
            self.descriptor.height,
            self.cluts.len(),
        )
    }
}

#[derive(Debug)]
pub struct PictureImageFile {
    images: Vec<Validated<PictureImage>>,
}

impl PictureImageFile {
    pub fn num_images(&self) -> usize {
        self.images.len()
    }

    pub fn get(&self, index: usize) -> Option<&Validated<PictureImage>> {
        self.images.get(index)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Validated<PictureImage>> {
        self.images.iter()
    }
}

impl Index<usize> for PictureImageFile {
    type Output = Validated<PictureImage>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.images[index]
    }
}

impl Readable for PictureImageFile {
    fn read<F: Read + Seek>(mut source: F) -> Result<Validated<Self>> {
        let mut descriptors: Vec<ImageDescriptor> = vec![];
        while descriptors.last().map(|d| d.header_count).unwrap_or(2) > 1 {
            descriptors.push(ImageDescriptor::read(&mut source)?);
        }

        let mut images = vec![];
        for descriptor in descriptors {
            let mut image = vec![0u8; descriptor.image_block_length as usize];
            source.seek(SeekFrom::Start(descriptor.image_block_offset as u64))?;
            source.read_exact(&mut image)?;

            // recorded CLUT block length does not seem to be reliable
            let mut clut = vec![0u8; descriptor.calc_clut_block_length()];
            if descriptor.pixel_type.has_clut() {
                source.seek(SeekFrom::Start(descriptor.clut_block_offset as u64))?;
                source.read_exact(&mut clut)?;
            }

            images.push(PictureImage::decode(descriptor, &clut, &image));
        }

        let warnings = Validated::combine(&images);
        Ok(Validated {
            object: Self { images },
            warnings,
        })
    }
}