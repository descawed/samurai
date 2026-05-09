use std::path::Path;

use anyhow::anyhow;

use crate::texture::{PictureImageFile, StackDirection};
use crate::Readable;

pub fn list_texture(path: &Path) -> anyhow::Result<()> {
    let images = PictureImageFile::load(path)?;
    for (i, image) in images.iter().enumerate() {
        println!("{}: {}", i, image);
    }

    Ok(())
}

pub fn export_texture(
    texture_path: &Path,
    output_path: &Path,
    format: &str,
    indexes: Vec<usize>,
    cluts: Vec<usize>,
    stack_direction: Option<StackDirection>,
) -> anyhow::Result<()> {
    let images = PictureImageFile::load(texture_path)?.object;
    let is_single_image = images.num_variants() == 1
        || (indexes.len() == 1
        && (cluts.len() == 1
        || stack_direction.is_some()
        || images.get(indexes[0]).is_none_or(|i| i.num_cluts() <= 1)));

    if !is_single_image && output_path.exists() && !output_path.is_dir() {
        return Err(anyhow!(
            "Output path {} must be a directory when exporting more than one image",
            output_path.display()
        ));
    }

    let filename = texture_path.file_name().unwrap().to_string_lossy();
    for (i, picture) in images.into_iter().enumerate() {
        if !indexes.is_empty() && !indexes.contains(&i) {
            continue;
        }

        let picture = match picture.ok() {
            Ok(picture) => picture,
            Err(e) => {
                eprintln!("Could not export image {}: {}", i, e);
                continue;
            }
        };

        let num_cluts = if stack_direction.is_some() {
            1
        } else {
            picture.num_variants()
        };
        for j in 0..num_cluts {
            if !cluts.is_empty() && !cluts.contains(&j) {
                continue;
            }

            let image = match stack_direction {
                Some(dir) => picture.to_image_all_cluts(dir),
                None => picture.to_image_with_clut(j),
            };
            if is_single_image && !output_path.is_dir() {
                image.save(output_path)?;
                return Ok(());
            }

            let image_path = output_path.join(format!("{}_{}_{}.{}", filename, i, j, format,));
            image.save(image_path)?;
        }
    }

    Ok(())
}