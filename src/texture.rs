use std::borrow::Cow;
use std::fmt;
use std::fmt::Formatter;
use std::io::{Read, Seek, SeekFrom};
use std::ops::Index;

use crate::{Readable, Validated};
use anyhow::{Result, anyhow};
use binrw::{BinRead, binrw};
use image::{DynamicImage, RgbaImage, imageops};

/// Width of a PSMCT32 column in pixels
const PSMCT32_COLUMN_WIDTH: usize = 8;
/// Height of a PSMCT32 column
const PSMCT32_COLUMN_HEIGHT: usize = 2;
/// Width of a PSMCT32 block
const PSMCT32_BLOCK_WIDTH: usize = PSMCT32_COLUMN_WIDTH;
/// Height of a PSMCT32 block
const PSMCT32_BLOCK_HEIGHT: usize = 8;
/// Width of a PSMCT32 page
const PSMCT32_PAGE_WIDTH: usize = 64;
/// Height of a PSMCT32 page
const PSMCT32_PAGE_HEIGHT: usize = 32;
/// Width of a PSMCT32 page in blocks
const PSMCT32_PAGE_WIDTH_IN_BLOCKS: usize = PSMCT32_PAGE_WIDTH / PSMCT32_BLOCK_WIDTH;
/// Number of blocks in a PSMCT32 page (= GS block count, same for any storage format).
const PSMCT32_PAGE_BLOCKS: usize = 32;
/// Size of a GS block in bytes. Texture base pointers (the offset that lets a second image share
/// the previous image's data buffer) are expressed in these units.
const GS_BLOCK_SIZE: usize = 256;

const fn scale_alpha(alpha: u8) -> u8 {
    if alpha > 128 {
        255
    } else {
        ((alpha as u16 * 255) / 128) as u8
    }
}

fn interleave<T>(data: &mut [T], elem_size: usize) {
    // TODO: I'm not super clear on why this is needed with image data. are the 8 and 2 here the
    //  8x2 size of a PSMCT32 column? find out and update to use constants if so.
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

/// Map an index in a WxH index column to the equivalent index in an 8x2 PSMCT32 column.
///
/// All units are in indexes, regardless of the number of bits an index spans. For odd-numbered
/// columns, flip bit value 4 in the input for correct results. The input must be in the range 0..W*H.
///
/// This implements the mapping described in section 8.6 Pixel Storage Format Conversion of the GS
/// User's Manual.
const fn psmt_map<const W: usize, const H: usize>(i: usize) -> usize {
    let row_size = W * H / PSMCT32_COLUMN_HEIGHT;

    let word_size = row_size / PSMCT32_COLUMN_WIDTH;
    let word_mask = PSMCT32_COLUMN_WIDTH - 1;
    let num_word_bits = PSMCT32_COLUMN_WIDTH.trailing_zeros() as usize;

    let num_column_pairs = word_size / 2; // indexes are stored in columns in an alternating order
    let num_column_bits = num_column_pairs.trailing_zeros() as usize; // how many bits do we need to index all the column pairs?
    let column_pair_mask = (1usize << num_column_bits) - 1;

    let row_shift = num_column_bits + num_word_bits;
    let odd_column_shift = row_shift + 1;

    let odd_column = (i >> odd_column_shift) & 1;
    ((i ^ (odd_column << 2)) & word_mask) * word_size // word select, swapping each group of 4 once we reach the second half of the block
        + ((i >> num_word_bits) & column_pair_mask) * 2 // column pair select
        + ((i >> row_shift) & 1) * row_size // row select
        + odd_column // odd column select
}

/// Unswizzle swizzled index data.
///
/// `tex_packed_width` and `buf_packed_width` differ only for *mixed-mode* images, where a second
/// texture is packed into the same byte buffer as a previous, wider one. In that case the texture's
/// own buffer width drives output→VRAM-block addressing while the underlying buffer's width drives
/// VRAM-block→file-byte addressing. For ordinary single-image files the two are equal and the
/// formula reduces to a straight 2-D row-major decode.
///
/// # Arguments
///
/// * `input` - The swizzled PSMCT32 data, decomposed into index-sized chunks
/// * `tex_packed_width` - Width of *this* texture's logical buffer in PSMCT32 pixels (i.e. the
///   value the GS would put in TEX0.TBW × 64 when reading the texture). Must be a multiple of
///   `PSMCT32_PAGE_WIDTH`.
/// * `buf_packed_width` - Width of the underlying (shared) byte buffer in PSMCT32 pixels — i.e. the
///   width of the first descriptor's image block, since that's the layout the bytes were written
///   in. For non-mixed-mode images, equal to `tex_packed_width`. Must be a multiple of
///   `PSMCT32_PAGE_WIDTH`.
/// * `tbp_blocks` - Texture base pointer in 256-byte GS blocks (0 for non-mixed-mode).
/// * `output_width` - Width of the output image in pixels
/// * `output_height` - Height of the output image in pixels
/// * `format` - The pixel storage mode of the unswizzled data
///
/// # Returns
///
/// The unswizzled indexes. Indexes whose source position falls outside `input` are returned as 0.
fn unswizzle<T: Into<usize> + Copy>(
    input: &[T],
    tex_packed_width: usize,
    buf_packed_width: usize,
    tbp_blocks: usize,
    output_width: usize,
    output_height: usize,
    format: PixelStorageMode,
) -> Vec<usize> {
    let output_size = output_width * output_height;
    let mut out = vec![0usize; output_size];

    let (page_width, page_height) = format.page_size();
    let (block_width, block_height) = format.block_size();
    let (column_width, column_height) = format.column_size();
    let pixels_per_word = format.num_pixels_per_word();
    let output_page_width_in_blocks = page_width / block_width;
    let block_transform = format.psmct32_block_transform();

    let tex_pages_wide = tex_packed_width / PSMCT32_PAGE_WIDTH;
    let buf_pages_wide = buf_packed_width / PSMCT32_PAGE_WIDTH;
    let buf_width_in_indexes = buf_packed_width * pixels_per_word;

    // PSMT4 packs two indexes per byte, so block-address arithmetic needs to be in indexes too.
    let indexes_per_block = GS_BLOCK_SIZE * pixels_per_word / 4; // 4 = bytes per PSMCT32 word
    let indexes_per_page_block = indexes_per_block; // 1 GS block = 1 swizzling block, regardless of format
    // Above two lines are equal — kept separate for readability of the address computation below.
    let _ = indexes_per_page_block;

    for (i, b) in out.iter_mut().enumerate() {
        let output_pixel_x = i % output_width;
        let output_pixel_y = i / output_width;

        // 1. Compute this texture's logical page coords and linearize using the texture's own width.
        let page_x = output_pixel_x / page_width;
        let page_y = output_pixel_y / page_height;
        let tex_page_index = page_y * tex_pages_wide + page_x;

        // 2. Within-page block, transformed from this format's layout into the linear PSMCT32-page
        //    block layout used by the file format.
        let output_block_x = (output_pixel_x % page_width) / block_width;
        let output_block_y = (output_pixel_y % page_height) / block_height;
        let output_block_index = output_block_y * output_page_width_in_blocks + output_block_x;
        let in_page_block_index = block_transform[output_block_index];

        // 3. Address the GS block in the shared buffer (TBP + texture's page contribution +
        //    within-page block), then re-linearize that block address into a 2-D position within
        //    the *underlying* buffer.
        let block_addr = tbp_blocks + tex_page_index * PSMCT32_PAGE_BLOCKS + in_page_block_index;
        let buf_page_index = block_addr / PSMCT32_PAGE_BLOCKS;
        let buf_within_page_block = block_addr % PSMCT32_PAGE_BLOCKS;
        let src_page_x = buf_page_index % buf_pages_wide;
        let src_page_y = buf_page_index / buf_pages_wide;
        let src_block_x = buf_within_page_block % PSMCT32_PAGE_WIDTH_IN_BLOCKS;
        let src_block_y = buf_within_page_block / PSMCT32_PAGE_WIDTH_IN_BLOCKS;

        // 4. Within-block, the format's own column layout determines which byte/nibble a pixel
        //    reads from.
        let column_index = (output_pixel_y % block_height) / column_height;
        let output_pixel_x_in_column = output_pixel_x % column_width;
        let output_pixel_y_in_column = output_pixel_y % column_height;
        let output_pixel_index_in_column =
            output_pixel_y_in_column * column_width + output_pixel_x_in_column;
        let input_pixel_index_in_column =
            format.psmt_map(output_pixel_index_in_column, column_index);
        let input_pixel_x_in_column =
            input_pixel_index_in_column % (PSMCT32_COLUMN_WIDTH * pixels_per_word);
        let input_pixel_y_in_column =
            input_pixel_index_in_column / (PSMCT32_COLUMN_WIDTH * pixels_per_word);

        // 5. Final flat index into the source data, addressed as a 2-D row-major buffer of the
        //    underlying width.
        let input_pixel_index = src_page_y * PSMCT32_PAGE_HEIGHT * buf_width_in_indexes
            + src_page_x * PSMCT32_PAGE_WIDTH * pixels_per_word
            + src_block_y * PSMCT32_BLOCK_HEIGHT * buf_width_in_indexes
            + src_block_x * PSMCT32_BLOCK_WIDTH * pixels_per_word
            + column_index * PSMCT32_COLUMN_HEIGHT * buf_width_in_indexes
            + input_pixel_y_in_column * buf_width_in_indexes
            + input_pixel_x_in_column;

        // For mixed-mode images the texture's nominal dimensions can extend past the end of the
        // shared buffer; treat out-of-range reads as transparent (index 0) rather than erroring.
        if let Some(value) = input.get(input_pixel_index) {
            *b = (*value).into();
        }
    }

    out
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
    /// Page size in pixels (width, height)
    pub const fn page_size(&self) -> (usize, usize) {
        match self {
            PixelStorageMode::PSMCT32
            | PixelStorageMode::PSMCT24
            | PixelStorageMode::PSMZ32
            | PixelStorageMode::PSMZ24 => (64, 32),
            PixelStorageMode::PSMCT16
            | PixelStorageMode::PSMCT16S
            | PixelStorageMode::PSMZ16
            | PixelStorageMode::PSMZ16S => (64, 64),
            PixelStorageMode::PSMT8H | PixelStorageMode::PSMT8 => (128, 64),
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH | PixelStorageMode::PSMT4 => {
                (128, 128)
            }
        }
    }

    /// Block size in pixels (width, height)
    pub const fn block_size(&self) -> (usize, usize) {
        match self {
            PixelStorageMode::PSMCT32
            | PixelStorageMode::PSMCT24
            | PixelStorageMode::PSMZ32
            | PixelStorageMode::PSMZ24 => (8, 8),
            PixelStorageMode::PSMCT16
            | PixelStorageMode::PSMCT16S
            | PixelStorageMode::PSMZ16
            | PixelStorageMode::PSMZ16S => (16, 8),
            PixelStorageMode::PSMT8H | PixelStorageMode::PSMT8 => (16, 16),
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH | PixelStorageMode::PSMT4 => {
                (32, 16)
            }
        }
    }

    /// Column size in pixels (width, height)
    pub const fn column_size(&self) -> (usize, usize) {
        match self {
            PixelStorageMode::PSMCT32
            | PixelStorageMode::PSMCT24
            | PixelStorageMode::PSMZ32
            | PixelStorageMode::PSMZ24 => (8, 2),
            PixelStorageMode::PSMCT16
            | PixelStorageMode::PSMCT16S
            | PixelStorageMode::PSMZ16
            | PixelStorageMode::PSMZ16S => (16, 2),
            PixelStorageMode::PSMT8H | PixelStorageMode::PSMT8 => (16, 4),
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH | PixelStorageMode::PSMT4 => {
                (32, 4)
            }
        }
    }

    // 8.6 Pixel Storage Format Conversion
    pub const fn psmt_map(&self, i: usize, column_index: usize) -> usize {
        // odd rows use an altered mapping where each group of 4 is swapped with its neighbor
        let i = i ^ ((column_index & 1) * 4);
        match self {
            PixelStorageMode::PSMCT32
            | PixelStorageMode::PSMCT24
            | PixelStorageMode::PSMZ32
            | PixelStorageMode::PSMZ24 => psmt_map::<8, 2>(i),
            PixelStorageMode::PSMCT16
            | PixelStorageMode::PSMCT16S
            | PixelStorageMode::PSMZ16
            | PixelStorageMode::PSMZ16S => psmt_map::<16, 2>(i),
            PixelStorageMode::PSMT8H | PixelStorageMode::PSMT8 => psmt_map::<16, 4>(i),
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH | PixelStorageMode::PSMT4 => {
                psmt_map::<32, 4>(i)
            }
        }
    }

    pub const fn psmct32_block_transform(&self) -> [usize; 32] {
        match self {
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH | PixelStorageMode::PSMT4 => [
                0, 8, 16, 24, 1, 9, 17, 25, 2, 10, 18, 26, 3, 11, 19, 27, 4, 12, 20, 28, 5, 13, 21,
                29, 6, 14, 22, 30, 7, 15, 23, 31,
            ],
            _ => [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 26, 27, 28, 29, 30, 31,
            ],
        }
    }

    pub const fn has_transparency(&self) -> bool {
        matches!(
            self,
            PixelStorageMode::PSMCT32 | PixelStorageMode::PSMCT16 | PixelStorageMode::PSMCT16S
        )
    }

    pub const fn has_clut(&self) -> bool {
        matches!(
            self,
            PixelStorageMode::PSMT8
                | PixelStorageMode::PSMT4
                | PixelStorageMode::PSMT8H
                | PixelStorageMode::PSMT4HL
                | PixelStorageMode::PSMT4HH
        )
    }

    pub const fn num_clut_colors(&self) -> usize {
        match self {
            PixelStorageMode::PSMT8H | PixelStorageMode::PSMT8 => 256,
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH | PixelStorageMode::PSMT4 => 16,
            _ => 0,
        }
    }

    pub const fn num_clut_bytes(&self, other: Self) -> usize {
        match (self.has_clut(), other.has_clut()) {
            (true, false) => self.num_clut_colors() * other.pixel_size().unwrap(),
            (false, true) => other.num_clut_colors() * self.pixel_size().unwrap(),
            _ => 0,
        }
    }

    pub const fn num_index_bytes(&self, width: usize, height: usize) -> usize {
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

    pub const fn num_pixels_per_word(&self) -> usize {
        match self {
            PixelStorageMode::PSMCT32
            | PixelStorageMode::PSMCT24
            | PixelStorageMode::PSMZ32
            | PixelStorageMode::PSMZ24 => 1,
            PixelStorageMode::PSMCT16
            | PixelStorageMode::PSMCT16S
            | PixelStorageMode::PSMZ16
            | PixelStorageMode::PSMZ16S => 2,
            PixelStorageMode::PSMT8H | PixelStorageMode::PSMT8 => 4,
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH | PixelStorageMode::PSMT4 => 8,
        }
    }

    pub const fn pixel_size(&self) -> Option<usize> {
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

    pub fn read_indexes(
        &self,
        data: &[u8],
        tex_packed_width: usize,
        buf_packed_width: usize,
        tbp_blocks: usize,
        output_width: usize,
        output_height: usize,
    ) -> Result<Vec<usize>> {
        match self {
            PixelStorageMode::PSMT8 | PixelStorageMode::PSMT8H => Ok(unswizzle(
                data,
                tex_packed_width,
                buf_packed_width,
                tbp_blocks,
                output_width,
                output_height,
                *self,
            )),
            PixelStorageMode::PSMT4 => {
                let indexes: Vec<_> = data
                    .iter()
                    .flat_map(|b| [(*b & 0xf) as usize, (*b >> 4) as usize])
                    .collect();
                Ok(unswizzle(
                    &indexes,
                    tex_packed_width,
                    buf_packed_width,
                    tbp_blocks,
                    output_width,
                    output_height,
                    *self,
                ))
            }
            PixelStorageMode::PSMT4HL | PixelStorageMode::PSMT4HH => Ok(data
                .iter()
                .flat_map(|b| [(*b & 0xf) as usize, (*b >> 4) as usize])
                .collect()),
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
    pub width_log2: u16,
    pub height_log2: u16,
    pub unknown0c: u16,
    pub unknown0e: u16,
    /// PSMCT32 width
    pub packed_width: u16,
    /// PSMCT32 height
    pub packed_height: u16,
    pub image_block_length: u32,
    pub image_block_offset: u32,
    pub num_cluts: u16,
    pub unknown1a: u16,
    pub clut_block_length: u32,
    pub clut_block_offset: u32,
    pub header_count: u16,
    /// Texture base pointer in 256-byte GS blocks
    pub tbp_blocks: u16,
    pub unknown2c: u32,
}

impl ImageDescriptor {
    pub const fn calc_clut_block_length(&self) -> usize {
        self.num_cluts as usize * self.pixel_type.num_clut_bytes(self.clut_pixel_type)
    }

    pub fn calc_image_block_length(&self) -> usize {
        self.pixel_type
            .num_image_bytes(self.pixel_width(), self.pixel_height())
    }

    pub const fn has_transparency(&self) -> bool {
        self.pixel_type.has_transparency()
            || (self.pixel_type.has_clut() && self.clut_pixel_type.has_transparency())
    }

    pub const fn has_clut(&self) -> bool {
        self.pixel_type.has_clut()
    }

    pub fn index_type(&self) -> Option<PixelStorageMode> {
        self.pixel_type.has_clut().then_some(self.pixel_type)
    }

    pub const fn pixel_type(&self) -> PixelStorageMode {
        if self.pixel_type.has_clut() {
            self.clut_pixel_type
        } else {
            self.pixel_type
        }
    }

    pub const fn pixel_width(&self) -> usize {
        1 << self.width_log2
    }

    pub const fn pixel_height(&self) -> usize {
        1 << self.height_log2
    }

    pub const fn packed_width(&self) -> usize {
        self.packed_width as usize
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
    fn decode(
        descriptor: ImageDescriptor,
        clut: &[u8],
        image: &[u8],
        buf_packed_width: usize,
        tbp_blocks: usize,
    ) -> Validated<Self> {
        let mut warnings = vec![];

        // For non-mixed-mode images, the image buffer should be at least as long as the declared
        // image data. For mixed-mode (tbp_blocks > 0), the shared buffer may be shorter than the
        // sum of the constituent images and out-of-range pixels are filled with index 0; skip the
        // length check in that case.
        if tbp_blocks == 0 {
            let expected_image_block_length = descriptor.calc_image_block_length();
            if image.len() < expected_image_block_length {
                warnings.push(format!(
                    "Image buffer is too small; expected at least {} bytes, got {} bytes",
                    expected_image_block_length,
                    image.len()
                ));
            }
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
                interleave(clut, 1);
            }

            ImageData::Indexes(
                match descriptor.pixel_type.read_indexes(
                    image,
                    descriptor.packed_width(),
                    buf_packed_width,
                    tbp_blocks,
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
        // For mixed-mode files, a descriptor with both image_block_length and image_block_offset
        // set to 0 reuses the previous descriptor's image bytes; its tbp_blocks field is the GS
        // texture base pointer (in 256-byte blocks) within that shared buffer. The bytes were
        // physically laid out using the previous descriptor's width, so we pass that as the buffer
        // width to the unswizzler — the texture's own packed_width controls how the GS would have
        // *read* the texture, while the buffer width controls where the bytes actually live.
        let mut prev_image: Vec<u8> = vec![];
        let mut prev_packed_width: usize = 0;
        for descriptor in descriptors {
            let (image, buf_packed_width, tbp_blocks) =
                if descriptor.image_block_length == 0 && descriptor.image_block_offset == 0 {
                    (
                        prev_image,
                        prev_packed_width,
                        descriptor.tbp_blocks as usize,
                    )
                } else {
                    let mut image = vec![0u8; descriptor.image_block_length as usize];
                    source.seek(SeekFrom::Start(descriptor.image_block_offset as u64))?;
                    source.read_exact(&mut image)?;
                    let pw = descriptor.packed_width();
                    prev_packed_width = pw;
                    (image, pw, 0)
                };

            // recorded CLUT block length does not seem to be reliable
            let mut clut = vec![0u8; descriptor.calc_clut_block_length()];
            if descriptor.pixel_type.has_clut() {
                source.seek(SeekFrom::Start(descriptor.clut_block_offset as u64))?;
                source.read_exact(&mut clut)?;
            }

            images.push(PictureImage::decode(
                descriptor,
                &clut,
                &image,
                buf_packed_width,
                tbp_blocks,
            ));

            prev_image = image;
        }

        let warnings = Validated::combine(&images);
        Ok(Validated {
            object: Self { images },
            warnings,
        })
    }
}
