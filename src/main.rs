use std::fs;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process;

use anyhow::{anyhow, Result};
use clap::{arg, Arg, ArgAction, Command};
use walkdir::WalkDir;

use samurai::texture::PictureImageFile;
use samurai::volume::{Volume, DEFAULT_MAX_OBJECTS};
use samurai::{script, Readable};

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
                            arg!(<VOLUME> "Path to volume.dat")
                                .value_parser(clap::value_parser!(PathBuf)),
                        ),
                )
                .subcommand(
                    Command::new("validate")
                        .about("Validate a volume.dat file")
                        .arg(
                            Arg::new("quiet")
                                .short('q')
                                .long("quiet")
                                .help("Suppress output when no issues are detected")
                                .action(ArgAction::SetTrue)
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
                            Arg::new("unformat_scripts")
                                .short('u')
                                .long("unformat-scripts")
                                .help("Reverse the effect of formatting scripts when the volume was unpacked")
                                .action(ArgAction::SetTrue)
                        )
                        .arg(
                            Arg::new("max_objects")
                                .short('m')
                                .long("max-objects")
                                .help("Maximum number of objects to reserve space for in the volume header")
                                .value_parser(clap::value_parser!(u32))
                        )
                        .arg(
                            Arg::new("verbose")
                                .short('v')
                                .long("verbose")
                                .help("Print a listing of files as they're packed")
                                .action(ArgAction::SetTrue)
                        )
                        .arg(arg!(<VOLUME> "Path to volume.dat to be created").value_parser(clap::value_parser!(PathBuf)))
                        .arg(arg!(<INPUT> ... "One or more input directories to pack").value_parser(clap::value_parser!(PathBuf))),
                )
                .subcommand(
                    Command::new("unpack")
                        .about("Unpack the contents of volume.dat")
                        // not using the arg macro here because rustfmt screws up the long option
                        .arg(
                            Arg::new("format_scripts")
                                .short('f')
                                .long("format-scripts")
                                .help("Format scripts for readability")
                                .action(ArgAction::SetTrue)
                        )
                        .arg(
                            Arg::new("tab_width")
                                .short('t')
                                .long("tab-width")
                                .help("If provided, lines will be indented with the requested number of spaces instead of tabs")
                                .value_parser(clap::value_parser!(usize))
                                .requires("format_scripts")
                        )
                        .arg(
                            Arg::new("verbose")
                                .short('v')
                                .long("verbose")
                                .help("Print a listing of files as they're unpacked")
                                .action(ArgAction::SetTrue)
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
                            Arg::new("tab_width")
                                .short('t')
                                .long("tab-width")
                                .help("If provided, lines will be indented with the requested number of spaces instead of tabs")
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
                            Arg::new("index")
                                .short('i')
                                .long("image")
                                .help("An index of an image in the texture to extract. Zero-based. May be specified multiple times.")
                                .value_parser(clap::value_parser!(usize))
                        )
                        .arg(
                            Arg::new("clut")
                                .short('c')
                                .long("clut")
                                .help("An index of a CLUT to use when exporting the image. Zero-based. May be specified multiple times.")
                                .value_parser(clap::value_parser!(usize))
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

fn list_volume(path: &Path) -> Result<()> {
    let volume = Volume::load(path)?;
    let mut names: Vec<_> = volume.iter().map(|(n, _)| n).collect();
    names.sort();

    for name in names {
        println!("{}", name);
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
) -> Result<()> {
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
            let (data, verbose_prefix) = if is_script && unformat_scripts {
                (
                    script::unformat_script(&fs::read_to_string(path)?),
                    "Unformatted and packed script file",
                )
            } else {
                (fs::read(path)?, "Packed")
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

fn main() -> Result<()> {
    let matches = cli().get_matches();

    match matches.subcommand() {
        Some(("volume", sub_matches)) => match sub_matches.subcommand() {
            Some(("list", list_matches)) => {
                let volume_path = list_matches
                    .get_one::<PathBuf>("VOLUME")
                    .expect("Path to volume.dat is required");

                list_volume(volume_path)?
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

                let unformat_scripts = pack_matches.get_flag("unformat_scripts");
                let max_objects = pack_matches
                    .get_one::<u32>("max_objects")
                    .copied()
                    .unwrap_or(DEFAULT_MAX_OBJECTS);
                let verbose = pack_matches.get_flag("verbose");

                pack_volume(
                    volume_path,
                    import_paths,
                    unformat_scripts,
                    max_objects,
                    verbose,
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

                let format_scripts = unpack_matches.get_flag("format_scripts");
                let tab_width = unpack_matches.get_one::<usize>("tab_width");
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
                let tab_width = format_matches.get_one::<usize>("tab_width");
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
            Some(("export", export_matches)) => {}
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }

    Ok(())
}
