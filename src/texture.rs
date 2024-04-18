use std::borrow::Cow;
use std::fmt;
use std::fmt::Formatter;
use std::io::{Read, Seek, SeekFrom};
use std::ops::Index;

use crate::{Readable, Validated};
use anyhow::{anyhow, Result};
use binrw::{binrw, BinRead};
use image::{imageops, DynamicImage, RgbaImage};

// for even rows; swap every 4 indexes for odd
const PSMT8_MAP: [usize; 64] = [
    0, 4, 8, 12, 16, 20, 24, 28, //
    2, 6, 10, 14, 18, 22, 26, 30, //
    32, 36, 40, 44, 48, 52, 56, 60, //
    34, 38, 42, 46, 50, 54, 58, 62, //
    17, 21, 25, 29, 1, 5, 9, 13, //
    19, 23, 27, 31, 3, 7, 11, 15, //
    49, 53, 57, 61, 33, 37, 41, 45, //
    51, 55, 59, 63, 35, 39, 43, 47, //
];
const PSMT8_COLUMN_WIDTH: usize = 16;
const PSMT8_COLUMN_HEIGHT: usize = 4;
const PSMCT32_COLUMN_WIDTH: usize = 32; // in bytes
const PSMCT32_COLUMN_HEIGHT: usize = 2;

const fn scale_alpha(alpha: u8) -> u8 {
    if alpha > 128 {
        255
    } else {
        ((alpha as u16 * 255) / 128) as u8
    }
}

fn swizzle<T>(data: &mut [T], elem_size: usize) {
    let row = 8 * elem_size;
    let block = 2 * row;
    let step = 2 * block;
    for i in (row..data.len()).step_by(step) {
        let end = i + block;
        if end > data.len() {
            break;
        }

        data[i..end].rotate_right(row);
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
            PixelStorageMode::PSMT8 | PixelStorageMode::PSMT8H => area,
            PixelStorageMode::PSMT4 | PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH => {
                area.div_ceil(2)
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
            // FIXME: fix handling of alpha for the below two modes
            PixelStorageMode::PSMCT24 => Ok(data
                .chunks_exact(3)
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

    pub fn read_indexes(&self, data: &[u8], width: usize, height: usize) -> Result<Vec<usize>> {
        match self {
            PixelStorageMode::PSMT8 | PixelStorageMode::PSMT8H => {
                let area = width * height;
                let mut out = vec![0usize; area];
                // convert PSMCT32 back to PSMT8
                let block_8s_per_row = width / PSMT8_COLUMN_WIDTH;
                let block_32s_per_row = width / PSMCT32_COLUMN_WIDTH;
                for (i, b) in out.iter_mut().enumerate() {
                    let pixel_y = i / width;
                    // coordinates of the 16x4 block containing pixel i in the output (unswizzled) image
                    let block_8_x = (i % width) / PSMT8_COLUMN_WIDTH;
                    let block_8_y = pixel_y / PSMT8_COLUMN_HEIGHT;
                    // index of the block in the list of all blocks
                    let block_index = block_8_y * block_8s_per_row + block_8_x;
                    // decompose into coordinates of the corresponding 32-bit 8x2 (i.e.
                    // 32x2 bytes) block in the input (swizzled) image
                    let block_32_x = block_index % block_32s_per_row;
                    let block_32_y = block_index / block_32s_per_row;
                    // index of the pixel within the 16x4 block
                    let x_in_block_8 = i % PSMT8_COLUMN_WIDTH;
                    let y_in_block_8 = pixel_y % PSMT8_COLUMN_HEIGHT;
                    // odd rows use an altered mapping where the first and second half of each
                    // group of 8 are swapped
                    let block_8_pixel =
                        (y_in_block_8 * PSMT8_COLUMN_WIDTH + x_in_block_8) ^ ((block_8_y & 1) << 2);
                    // index of the corresponding pixel in the 32-bit block
                    let block_32_pixel = PSMT8_MAP[block_8_pixel];
                    let x_in_block_32 = block_32_pixel % PSMCT32_COLUMN_WIDTH;
                    let y_in_block_32 = block_32_pixel / PSMCT32_COLUMN_WIDTH;
                    // absolute index of pixel in input image
                    let in_index = (block_32_y * PSMCT32_COLUMN_HEIGHT + y_in_block_32) * width
                        + (block_32_x * PSMCT32_COLUMN_WIDTH + x_in_block_32);
                    *b = data[in_index] as usize;
                }

                // honestly not sure why this is necessary
                swizzle(&mut out, width / 16);

                Ok(out)
            }
            PixelStorageMode::PSMT4 | PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH => {
                Ok(data
                    .iter()
                    .flat_map(|b| [(*b & 0xf) as usize, (*b >> 4) as usize])
                    .collect())
            }
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
            .num_image_bytes(self.pixel_width(), self.pixel_height())
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

    pub fn pixel_width(&self) -> usize {
        // FIXME: need this for other modes?
        (if matches!(
            self.pixel_type,
            PixelStorageMode::PSMT8 | PixelStorageMode::PSMT8H
        ) {
            self.width * 2
        } else {
            self.width
        }) as usize
    }

    pub fn pixel_height(&self) -> usize {
        // FIXME: need this for other modes?
        (if matches!(
            self.pixel_type,
            PixelStorageMode::PSMT8 | PixelStorageMode::PSMT8H
        ) {
            self.height * 2
        } else {
            self.height
        }) as usize
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
        let mut cluts: Vec<Vec<_>> = Vec::with_capacity(num_cluts);
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

            // swizzle
            for clut in &mut cluts {
                swizzle(clut, 1);
            }

            ImageData::Indexes(
                match descriptor.pixel_type.read_indexes(
                    image,
                    descriptor.pixel_width(),
                    descriptor.pixel_height(),
                ) {
                    Ok(indexes) => indexes,
                    Err(e) => {
                        warnings.push(format!("Error reading indexes: {}", e));
                        vec![]
                    }
                },
            )
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

    pub fn num_variants(&self) -> usize {
        if self.num_cluts() == 0 {
            1
        } else {
            self.num_cluts()
        }
    }

    pub fn to_image_all_cluts(&self, stack: StackDirection) -> DynamicImage {
        let num_cluts = self.cluts.len();
        if num_cluts == 0 {
            return self.to_image();
        }

        let base_width = self.descriptor.pixel_width();
        let base_height = self.descriptor.pixel_height();
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
                self.descriptor.pixel_width() as u32,
                self.descriptor.pixel_height() as u32,
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
            self.descriptor.pixel_width(),
            self.descriptor.pixel_height(),
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

    pub fn num_variants(&self) -> usize {
        self.images.iter().map(|i| i.num_variants()).sum()
    }

    pub fn get(&self, index: usize) -> Option<&Validated<PictureImage>> {
        self.images.get(index)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Validated<PictureImage>> {
        self.images.iter()
    }
}

impl IntoIterator for PictureImageFile {
    type Item = Validated<PictureImage>;
    type IntoIter = <Vec<Validated<PictureImage>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.images.into_iter()
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
