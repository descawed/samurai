use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::BufWriter;
use std::path::{Path, PathBuf};
use std::{fs, process};

use anyhow::anyhow;
use strum::EnumString;
use walkdir::WalkDir;

use crate::Readable;
use crate::volume::{Volume, hash_name};

#[derive(Clone, Copy, Debug, EnumString)]
pub enum UnorderedBehavior {
    #[strum(serialize = "fail")]
    Fail,
    #[strum(serialize = "ignore")]
    Ignore,
    #[strum(serialize = "append")]
    Append,
}

pub fn list_volume(path: &Path, do_sort: bool, verbose: bool) -> anyhow::Result<()> {
    let volume = Volume::load(path)?;
    let mut names: Vec<_> = volume.iter().map(|(n, _)| n).collect();
    if do_sort {
        names.sort();
    }

    for name in names {
        if verbose {
            let data = volume.get(name).unwrap();
            let hash = hash_name(name.as_bytes());
            println!("{} (hash: {:08X}, {} bytes)", name, hash, data.len());
        } else {
            println!("{}", name);
        }
    }

    Ok(())
}

pub fn validate_volume(path: &Path, quiet: bool) -> anyhow::Result<()> {
    let warnings = Volume::load(path)?.warnings;
    if warnings.is_empty() {
        if !quiet {
            println!("Validation successful");
        }
    } else {
        for warning in warnings {
            eprintln!("{}", warning);
        }
        process::exit(1);
    }

    Ok(())
}

pub fn unpack_volume<S: AsRef<str>>(
    volume_path: &Path,
    extract_path: &Path,
    prefixes: Option<&[S]>,
    verbose: bool,
) -> anyhow::Result<()> {
    if extract_path.is_file() {
        return Err(anyhow!("Unpack path must be a directory"));
    }

    if !extract_path.exists() {
        fs::create_dir(extract_path)?;
    }

    let volume = Volume::load(volume_path)?;
    for (name, data) in volume.iter() {
        if let Some(prefix_list) = prefixes {
            let mut matched = false;
            for prefix in prefix_list {
                let prefix = prefix.as_ref();
                if name.starts_with(prefix) {
                    matched = true;
                }
            }

            if !matched {
                continue;
            }
        }

        let mut output_path = extract_path.to_path_buf();
        output_path.push(name.replace('\\', "/"));

        if let Some(parent) = output_path.parent()
            && !parent.exists()
        {
            fs::create_dir_all(parent)?;
        }

        fs::write(&output_path, data)?;

        if verbose {
            println!("Extracted {} to {}", name, output_path.display());
        }
    }

    Ok(())
}

pub fn pack_volume<T: AsRef<Path>, I: Iterator<Item = T>>(
    volume_path: &Path,
    import_paths: I,
    max_objects: u32,
    verbose: bool,
    order_path: Option<&Path>,
    unordered_behavior: UnorderedBehavior,
) -> anyhow::Result<()> {
    let mut paths = vec![];
    let mut volume_names = HashSet::new();
    let mut volume = Volume::new(max_objects);
    for import_path in import_paths {
        let import_path = import_path.as_ref();
        for entry in WalkDir::new(import_path).follow_links(true) {
            let entry = entry?;
            if entry.file_type().is_dir() {
                continue;
            }

            let path = entry.path();
            let Some(relative) = pathdiff::diff_paths(path, import_path) else {
                eprintln!(
                    "Not including {} because its path relative to {} could not be determined",
                    path.display(),
                    import_path.display()
                );
                continue;
            };

            // volume.dat always uses backslashes
            let volume_name = relative.to_string_lossy().replace('/', "\\");
            if !volume_names.insert(volume_name.clone()) {
                return Err(anyhow!("Duplicate input filename {}", volume_name));
            }
            paths.push((path.to_path_buf(), volume_name));
        }
    }

    let paths = match order_path {
        Some(order_path) => {
            let data = fs::read_to_string(order_path)?;
            let (ordered_names, not_found_names): (Vec<_>, Vec<_>) = data
                .split('\n')
                .filter(|n| !n.is_empty())
                .partition(|n| volume_names.contains(*n));

            if !not_found_names.is_empty() {
                eprintln!("Warning: the following names from the order file were not found:");
                for name in not_found_names {
                    eprintln!("\t{}", name);
                }
            }

            let indexes: HashMap<_, _> = ordered_names
                .into_iter()
                .enumerate()
                .map(|(i, n)| (n, i))
                .collect();

            let mut new_paths = vec![(PathBuf::new(), String::new()); paths.len()];
            let mut num_appended = 0usize;
            for path_info in paths {
                let new_index = {
                    let name = path_info.1.as_str();
                    match (indexes.get(&name), unordered_behavior) {
                        (Some(new_index), _) => *new_index,
                        (None, UnorderedBehavior::Fail) => {
                            return Err(anyhow!("{} not found in order file", name));
                        }
                        (None, UnorderedBehavior::Ignore) => {
                            new_paths.pop();
                            continue;
                        }
                        (None, UnorderedBehavior::Append) => {
                            num_appended += 1;
                            new_paths.len() - num_appended
                        }
                    }
                };

                new_paths[new_index] = path_info;
            }

            new_paths
        }
        None => {
            // default to alphabetical sort
            // FIXME: this should sort by Shift JIS codepoint, not Unicode codepoint
            paths.sort_by(|a, b| a.1.to_lowercase().cmp(&b.1.to_lowercase()));
            paths
        }
    };

    for (path, volume_name) in paths {
        let data = fs::read(&path)?;

        let hash = volume.add(volume_name.clone(), data)?;
        if verbose {
            println!(
                "Packed {} as {} (hash {:08X})",
                path.display(),
                volume_name,
                hash
            );
        }
    }

    let output_file = File::create(volume_path)?;
    let writer = BufWriter::new(output_file);
    volume.write(writer)
}
