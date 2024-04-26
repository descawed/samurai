use std::collections::{HashMap, HashSet};
use std::fs;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process;
use std::str::FromStr;

use anyhow::{anyhow, Error, Result};
use clap::{arg, Command};
use walkdir::WalkDir;

use samurai::texture::{PictureImageFile, StackDirection};
use samurai::volume::{hash_name, Volume, DEFAULT_MAX_OBJECTS};
use samurai::{script, Readable};

#[derive(Clone, Copy, Debug)]
enum UnorderedBehavior {
    Fail,
    Ignore,
    Append,
}

impl FromStr for UnorderedBehavior {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "fail" => Ok(Self::Fail),
            "ignore" => Ok(Self::Ignore),
            "append" => Ok(Self::Append),
            _ => Err(anyhow!("Unknown UnorderedBehavior {}", s)),
        }
    }
}

// rustfmt doesn't understand the arg! macro syntax
#[rustfmt::skip]
fn cli() -> Command {
    Command::new("samurai")
        .about("Manipulate files for the PS2 game (Way of the) Samurai")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .subcommand(
            Command::new("volume")
                .about("Pack or unpack volume.dat")
                .subcommand_required(true)
                .subcommand(
                    Command::new("list")
                        .about("List contents of volume.dat")
                        .arg(
                            arg!(-s --sort "Sort the output alphabetically")
                        )
                        .arg(
                            arg!(-v --verbose "Print additional information about each file")
                        )
                        .arg(
                            arg!(<VOLUME> "Path to volume.dat")
                                .value_parser(clap::value_parser!(PathBuf)),
                        ),
                )
                .subcommand(
                    Command::new("validate")
                        .about("Validate a volume.dat file")
                        .arg(
                            arg!(-q --quiet "Suppress output when no issues are detected")
                        )
                        .arg(
                            arg!(<VOLUME> "Path to volume.dat")
                                .value_parser(clap::value_parser!(PathBuf))
                        )
                )
                .subcommand(
                    Command::new("pack")
                        .about("Pack one or more directories into a volume")
                        .arg(
                            arg!(-u --"unformat-scripts" "Reverse the effect of formatting scripts when the volume was unpacked")
                        )
                        .arg(
                            arg!(-m --"max-objects" <MAX> "Maximum number of objects to reserve space for in the volume header")
                                .value_parser(clap::value_parser!(u32))
                        )
                        .arg(
                            arg!(-v --verbose "Print a listing of files as they're packed")
                        )
                        .arg(
                            arg!(-o --order <PATH> "Path to a text file with a newline-delimited list of filenames in the order they should be packed in the volume")
                                .value_parser(clap::value_parser!(PathBuf))
                        )
                        .arg(
                            arg!(-b --"unordered-behavior" <BEHAVIOR> "Action to take when an input file isn't found in the order file")
                                .default_value("fail")
                                .value_parser(["fail", "ignore", "append"])
                                .requires("order")
                        )
                        .arg(arg!(<VOLUME> "Path to volume.dat to be created").value_parser(clap::value_parser!(PathBuf)))
                        .arg(arg!(<INPUT> ... "One or more input directories to pack").value_parser(clap::value_parser!(PathBuf))),
                )
                .subcommand(
                    Command::new("unpack")
                        .about("Unpack the contents of volume.dat")
                        .arg(
                            arg!(-f --"format-scripts" "Format scripts for readability")
                        )
                        .arg(
                            arg!(-t --"tab-width" <WIDTH> "If provided, lines will be indented with the requested number of spaces instead of tabs")
                                .value_parser(clap::value_parser!(usize))
                                .requires("format-scripts")
                        )
                        .arg(
                            arg!(-v --verbose "Print a listing of files as they're unpacked")
                        )
                        .arg(
                            arg!(<VOLUME> "Path to volume.dat")
                                .value_parser(clap::value_parser!(PathBuf))
                        )
                        .arg(
                            arg!(<OUTPUT> "Path to a directory where the volume will be extracted")
                                .value_parser(clap::value_parser!(PathBuf)),
                        )
                        .arg(
                            arg!([PREFIX] ... "One or more prefixes to filter which files are unpacked.")
                        )
                ),
        )
        .subcommand(
            Command::new("script")
                .about("Format or unformat scripts")
                .subcommand_required(true)
                .subcommand(
                    Command::new("format").about("Format a raw script file for readability")
                        .arg(
                            arg!(-t --"tab-width" <WIDTH> "If provided, lines will be indented with the requested number of spaces instead of tabs")
                                .value_parser(clap::value_parser!(usize))
                        )
                        .arg(
                            arg!(<SCRIPT> "Path to script file")
                                .value_parser(clap::value_parser!(PathBuf)),
                        )
                        .arg(
                            arg!([OUTPUT] "Path to output file. Output is printed to stdout if omitted.")
                                .value_parser(clap::value_parser!(PathBuf)),
                        ),
                )
                .subcommand(
                    Command::new("unformat")
                        .about("Unformat a previously-formatted script for storage in volume.dat")
                        .arg(
                            arg!(<SCRIPT> "Path to script file")
                                .value_parser(clap::value_parser!(PathBuf)),
                        )
                        .arg(
                            arg!([OUTPUT] "Path to output file. Output is printed to stdout if omitted.")
                                .value_parser(clap::value_parser!(PathBuf)),
                        ),
                ),
        )
        .subcommand(
            Command::new("texture")
                .about("Convert textures to other formats")
                .subcommand_required(true)
                .subcommand(
                    Command::new("list")
                        .about("List stats and contents of a texture")
                        .arg(
                            arg!(<TEXTURE> "Path to texture file")
                                .value_parser(clap::value_parser!(PathBuf))
                        )
                )
                .subcommand(
                    Command::new("export")
                        .about("Export a texture image to another format")
                        .arg(
                            arg!(-i --index <INDEX> "An index of an image in the texture to extract. Zero-based. May be specified multiple times.")
                                .value_parser(clap::value_parser!(usize))
                        )
                        .arg(
                            arg!(-c --clut <INDEX> "An index of a CLUT to use when exporting the image. Zero-based. May be specified multiple times.")
                                .value_parser(clap::value_parser!(usize))
                        )
                        .arg(
                            arg!(-f --format <FORMAT> "The image format (file extension) to export to. Defaults to png. If exporting a single image, the file extension in the export path will override this.")
                                .default_value("png")
                        )
                        .arg(
                            arg!(-s --"stack-cluts" <DIR> "Stack all CLUTs into one export image either horizontally or vertically")
                                .value_parser(["h", "horizontal", "v", "vertical"])
                                .conflicts_with("clut")
                        )
                        .arg(
                            arg!(<TEXTURE> "Path to texture file")
                                .value_parser(clap::value_parser!(PathBuf))
                        )
                        .arg(
                            arg!(<OUTPUT> "Path to export location. Must be a directory unless exporting a single image with a single (or no) CLUT.")
                                .value_parser(clap::value_parser!(PathBuf))
                        )
                )
        )
}

fn list_volume(path: &Path, do_sort: bool, verbose: bool) -> Result<()> {
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

fn validate_volume(path: &Path, quiet: bool) -> Result<()> {
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

fn unpack_volume<S: AsRef<str>>(
    volume_path: &Path,
    extract_path: &Path,
    format_scripts: bool,
    tab_width: Option<usize>,
    prefixes: Option<&[S]>,
    verbose: bool,
) -> Result<()> {
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
        let mut is_script = None;
        for dir in name.split(&['/', '\\']) {
            if is_script.is_none() {
                is_script = Some(dir == "script");
            }
            output_path = output_path.join(dir);
        }
        let is_script = is_script.unwrap_or(false);

        if let Some(parent) = output_path.parent() {
            if !parent.exists() {
                fs::create_dir_all(parent)?;
            }
        }

        if is_script && format_scripts {
            fs::write(&output_path, script::format_script(data, tab_width))?;

            if verbose {
                println!(
                    "Formatted script file {} and extracted to {}",
                    name,
                    output_path.display()
                );
            }
        } else {
            fs::write(&output_path, data)?;

            if verbose {
                println!("Extracted {} to {}", name, output_path.display());
            }
        }
    }

    Ok(())
}

fn pack_volume<T: AsRef<Path>, I: Iterator<Item = T>>(
    volume_path: &Path,
    import_paths: I,
    unformat_scripts: bool,
    max_objects: u32,
    verbose: bool,
    order_path: Option<&Path>,
    unordered_behavior: UnorderedBehavior,
) -> Result<()> {
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

            let is_script = relative
                .iter()
                .next()
                .map_or(false, |d| d.to_string_lossy() == "script");
            // volume.dat always uses backslashes
            let volume_name = relative.to_string_lossy().replace('/', "\\");
            if !volume_names.insert(volume_name.clone()) {
                return Err(anyhow!("Duplicate input filename {}", volume_name));
            }
            paths.push((path.to_path_buf(), volume_name, is_script));
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

            let mut new_paths = vec![(PathBuf::new(), String::new(), false); paths.len()];
            let mut num_appended = 0usize;
            for path_info in paths {
                let new_index = {
                    let name = path_info.1.as_str();
                    match (indexes.get(&name), unordered_behavior) {
                        (Some(new_index), _) => *new_index,
                        (None, UnorderedBehavior::Fail) => {
                            return Err(anyhow!("{} not found in order file", name))
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

    for (path, volume_name, is_script) in paths {
        let (data, verbose_prefix) = if is_script && unformat_scripts {
            (
                script::unformat_script(&fs::read_to_string(&path)?),
                "Unformatted and packed script file",
            )
        } else {
            (fs::read(&path)?, "Packed")
        };

        let hash = volume.add(volume_name.clone(), data)?;
        if verbose {
            println!(
                "{} {} as {} (hash {:08X})",
                verbose_prefix,
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

fn format_script(
    script_path: &Path,
    output_path: Option<&Path>,
    tab_width: Option<usize>,
) -> Result<()> {
    let formatted = script::format_script(&fs::read(script_path)?, tab_width);
    if let Some(output_path) = output_path {
        fs::write(output_path, formatted)?;
    } else {
        print!("{}", formatted);
    }

    Ok(())
}

fn unformat_script(script_path: &Path, output_path: Option<&Path>) -> Result<()> {
    let raw = script::unformat_script(&fs::read_to_string(script_path)?);
    if let Some(output_path) = output_path {
        fs::write(output_path, raw)?;
    } else {
        std::io::stdout().write_all(&raw)?;
    }

    Ok(())
}

fn list_texture(path: &Path) -> Result<()> {
    let images = PictureImageFile::load(path)?;
    for (i, image) in images.iter().enumerate() {
        println!("{}: {}", i, image);
    }

    Ok(())
}

fn export_texture(
    texture_path: &Path,
    output_path: &Path,
    format: &str,
    indexes: Vec<usize>,
    cluts: Vec<usize>,
    stack_direction: Option<StackDirection>,
) -> Result<()> {
    let images = PictureImageFile::load(texture_path)?.object;
    let is_single_image = images.num_variants() == 1
        || (indexes.len() == 1
            && (cluts.len() == 1
                || stack_direction.is_some()
                || images.get(indexes[0]).map_or(true, |i| i.num_cluts() <= 1)));

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

fn main() -> Result<()> {
    let matches = cli().get_matches();

    match matches.subcommand() {
        Some(("volume", sub_matches)) => match sub_matches.subcommand() {
            Some(("list", list_matches)) => {
                let volume_path = list_matches
                    .get_one::<PathBuf>("VOLUME")
                    .expect("Path to volume.dat is required");

                let do_sort = list_matches.get_flag("sort");

                let verbose = list_matches.get_flag("verbose");

                list_volume(volume_path, do_sort, verbose)?;
            }
            Some(("validate", validate_matches)) => {
                let volume_path = validate_matches
                    .get_one::<PathBuf>("VOLUME")
                    .expect("Path to volume.dat is required");

                let quiet = validate_matches.get_flag("quiet");

                validate_volume(volume_path, quiet)?;
            }
            Some(("pack", pack_matches)) => {
                let volume_path = pack_matches
                    .get_one::<PathBuf>("VOLUME")
                    .expect("Path to volume.dat is required");

                let import_paths = pack_matches
                    .get_many::<PathBuf>("INPUT")
                    .expect("At least one input directory is required");

                let order_path = pack_matches
                    .get_one::<PathBuf>("order")
                    .map(PathBuf::as_path);

                let unordered_behavior = UnorderedBehavior::from_str(
                    pack_matches
                        .get_one::<String>("unordered-behavior")
                        .unwrap(),
                )?;

                let unformat_scripts = pack_matches.get_flag("unformat-scripts");
                let max_objects = pack_matches
                    .get_one::<u32>("max-objects")
                    .copied()
                    .unwrap_or(DEFAULT_MAX_OBJECTS);
                let verbose = pack_matches.get_flag("verbose");

                pack_volume(
                    volume_path,
                    import_paths,
                    unformat_scripts,
                    max_objects,
                    verbose,
                    order_path,
                    unordered_behavior,
                )?;
            }
            Some(("unpack", unpack_matches)) => {
                let volume_path = unpack_matches
                    .get_one::<PathBuf>("VOLUME")
                    .expect("Path to volume.dat is required");

                let extract_path = unpack_matches
                    .get_one::<PathBuf>("OUTPUT")
                    .expect("Path to extraction directory is required");

                let prefixes: Vec<_> = unpack_matches
                    .get_many::<String>("PREFIX")
                    .map(|v| v.map(|s| s.replace('/', "\\")).collect())
                    .unwrap_or(vec![]);

                let format_scripts = unpack_matches.get_flag("format-scripts");
                let tab_width = unpack_matches.get_one::<usize>("tab-width");
                let verbose = unpack_matches.get_flag("verbose");

                unpack_volume(
                    volume_path,
                    extract_path,
                    format_scripts,
                    tab_width.copied(),
                    if prefixes.is_empty() {
                        None
                    } else {
                        Some(&prefixes)
                    },
                    verbose,
                )?;
            }
            _ => unreachable!(),
        },
        Some(("script", sub_matches)) => match sub_matches.subcommand() {
            Some(("format", format_matches)) => {
                let script_path = format_matches
                    .get_one::<PathBuf>("SCRIPT")
                    .expect("Path to script file is required");
                let output_path = format_matches.get_one::<PathBuf>("OUTPUT");
                let tab_width = format_matches.get_one::<usize>("tab-width");
                format_script(
                    script_path,
                    output_path.map(PathBuf::as_path),
                    tab_width.copied(),
                )?;
            }
            Some(("unformat", unformat_matches)) => {
                let script_path = unformat_matches
                    .get_one::<PathBuf>("SCRIPT")
                    .expect("Path to script file is required");
                let output_path = unformat_matches.get_one::<PathBuf>("OUTPUT");
                unformat_script(script_path, output_path.map(PathBuf::as_path))?;
            }
            _ => unreachable!(),
        },
        Some(("texture", sub_matches)) => match sub_matches.subcommand() {
            Some(("list", list_matches)) => {
                let texture_path = list_matches
                    .get_one::<PathBuf>("TEXTURE")
                    .expect("Texture path is required");

                list_texture(texture_path.as_path())?;
            }
            Some(("export", export_matches)) => {
                let texture_path = export_matches
                    .get_one::<PathBuf>("TEXTURE")
                    .expect("Texture path is required");

                let output_path = export_matches
                    .get_one::<PathBuf>("OUTPUT")
                    .expect("Output path is required");

                let indexes = match export_matches.get_many::<usize>("index") {
                    Some(indexes) => indexes.copied().collect(),
                    None => vec![],
                };

                let cluts = match export_matches.get_many::<usize>("clut") {
                    Some(cluts) => cluts.copied().collect(),
                    None => vec![],
                };

                let format = export_matches.get_one::<String>("format").unwrap();

                let stack =
                    export_matches
                        .get_one::<String>("stack")
                        .and_then(|s| match s.as_str() {
                            "h" | "horizontal" => Some(StackDirection::Horizontal),
                            "v" | "vertical" => Some(StackDirection::Vertical),
                            _ => None,
                        });

                export_texture(texture_path, output_path, format, indexes, cluts, stack)?;
            }
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }

    Ok(())
}
