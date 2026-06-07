use std::path::PathBuf;
use std::str::FromStr;

use anyhow::Result;
use clap::{Command, arg};
use log::LevelFilter;

use samurai::cli::*;
use samurai::module::DEFAULT_ALIGNMENT;
use samurai::texture::StackDirection;
use samurai::volume::DEFAULT_MAX_OBJECTS;

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
                            arg!(-s --simple "Use the simple formatter instead of fully parsing the script and regenerating from the AST. Mutually exclusive with --config.")
                                .conflicts_with("config")
                        )
                        .arg(
                            arg!(-c --config <CONFIG> "Path to config.h. If provided, an include will be added and literal function arguments will be replaced with symbolic constants where appropriate.")
                                .value_parser(clap::value_parser!(PathBuf))
                        )
                        .arg(
                            arg!(-e --encoding <ENCODING> "The encoding of the input file. Can be utf-8, shift-jis, or detect. The output will always be UTF-8.")
                                .value_parser(["utf-8", "shift-jis", "detect"])
                                .default_value("detect")
                        )
                        .arg(
                            arg!(-q --quiet "Don't print warnings")
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
                            arg!(-e --encoding <ENCODING> "The encoding of the output file. Can be utf-8 or shift-jis. The input file must always be UTF-8.")
                                .value_parser(["utf-8", "shift-jis"])
                                .default_value("shift-jis")
                        )
                        .arg(
                            arg!(-c --config <CONFIG> "Path to config.h. If provided, the include of config.h from the formatter will be removed and symbolic constants from the config will be replaced with literals.")
                                .value_parser(clap::value_parser!(PathBuf))
                        )
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
        .subcommand(
            Command::new("module")
                .about("Pack or unpack MODULE.BIN")
                .subcommand_required(true)
                .subcommand(
                    Command::new("unpack")
                        .about("Unpack the contents of MODULE.BIN")
                        .arg(arg!(<ARCHIVE> "Path to MODULE.BIN archive").value_parser(clap::value_parser!(PathBuf)))
                        .arg(arg!(<OUTPUT> "Path to a directory where the MODULE.BIN will be extracted").value_parser(clap::value_parser!(PathBuf))),
                )
                .subcommand(
                    Command::new("pack")
                        .about("Pack one or more modules into a MODULE.BIN archive")
                        .arg(
                            arg!(-a --alignment "Byte alignment of the modules in the archive. Should be a power of 2.")
                                .value_parser(clap::value_parser!(u32))
                        )
                        .arg(arg!(<ARCHIVE> "Path to MODULE.BIN archive to be created").value_parser(clap::value_parser!(PathBuf)))
                        .arg(arg!(<INPUT> ... "One or more input modules to pack").value_parser(clap::value_parser!(PathBuf))),
                )
        )
        .subcommand(
            Command::new("debug")
                .about("Debug the game running in PCSX2")
        )
        .subcommand(
            Command::new("autosplitter")
                .about("Run a LiveSplit autosplitter for the game running in PCSX2")
                .arg(
                    arg!(-l --"live-split-port" <PORT> "Port that the LiveSplit server is running on")
                        .value_parser(clap::value_parser!(u16))
                        .default_value("16834")
                )
                .arg(
                    arg!(-u --"update-frequency" <MILLIS> "How often to update the state of the game, in milliseconds")
                        .value_parser(clap::value_parser!(u64))
                        .default_value("15")
                )
                .arg(
                    arg!(-e --ending <ENDING> "Target ending (1-6). If omitted, it's read from your splits' custom variables.")
                        .value_parser(clap::value_parser!(u8).range(1..=6))
                )
                .arg(
                    arg!(-n --"new-game" <TYPE> "Whether this is a New Game or New Game+ run. If omitted, it's read from your splits' custom variables.")
                        .value_parser(["ng", "ng+", "new-game", "new-game-plus"])
                )
                .arg(
                    arg!(-g --"log-level" <LEVEL> "What level of logging output to show")
                        .value_parser(["off", "trace", "debug", "info", "warn", "error"])
                        .default_value("info")
                )
        )
        .subcommand(
            Command::new("splits")
                .about("Generate LiveSplit splits files from the autosplitter routes")
                .arg(arg!(-s --"skip-existing" "Skip splits files that already exist in the destination directory"))
                .arg(
                    arg!(<PATH> "Path to the directory where the splits files will be created. Will be created if it doesn't exist.")
                        .value_parser(clap::value_parser!(PathBuf))
                )
        )
}

fn main() -> Result<()> {
    let matches = cli().get_matches();

    match matches.subcommand() {
        Some(("module", sub_matches)) => match sub_matches.subcommand() {
            Some(("unpack", unpack_matches)) => {
                let archive_path = unpack_matches
                    .get_one::<PathBuf>("ARCHIVE")
                    .expect("Path to MODULE.BIN archive is required");

                let extract_path = unpack_matches
                    .get_one::<PathBuf>("OUTPUT")
                    .expect("Path to extraction directory is required");

                unpack_modules(archive_path, extract_path)?;
            }
            Some(("pack", pack_matches)) => {
                let alignment = pack_matches
                    .get_one::<u32>("alignment")
                    .copied()
                    .unwrap_or(DEFAULT_ALIGNMENT);

                let archive_path = pack_matches
                    .get_one::<PathBuf>("ARCHIVE")
                    .expect("Path to MODULE.BIN archive is required");

                let input_paths = pack_matches
                    .get_many::<PathBuf>("INPUT")
                    .expect("At least one input module is required");

                pack_modules(archive_path, alignment, input_paths)?;
            }
            _ => unreachable!(),
        },
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

                let max_objects = pack_matches
                    .get_one::<u32>("max-objects")
                    .copied()
                    .unwrap_or(DEFAULT_MAX_OBJECTS);
                let verbose = pack_matches.get_flag("verbose");

                pack_volume(
                    volume_path,
                    import_paths,
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

                let verbose = unpack_matches.get_flag("verbose");

                unpack_volume(
                    volume_path,
                    extract_path,
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

                let use_simple_parser = format_matches.get_flag("simple");
                let config_path = format_matches.get_one::<PathBuf>("config");
                let encoding =
                    Encoding::from_str(format_matches.get_one::<String>("encoding").unwrap())?;
                let quiet = format_matches.get_flag("quiet");

                format_script(
                    script_path,
                    output_path.map(PathBuf::as_path),
                    tab_width.copied(),
                    use_simple_parser,
                    config_path.map(PathBuf::as_path),
                    encoding,
                    quiet,
                )?;
            }
            Some(("unformat", unformat_matches)) => {
                let script_path = unformat_matches
                    .get_one::<PathBuf>("SCRIPT")
                    .expect("Path to script file is required");
                let output_path = unformat_matches.get_one::<PathBuf>("OUTPUT");
                let encoding =
                    Encoding::from_str(unformat_matches.get_one::<String>("encoding").unwrap())?;
                let config_path = unformat_matches.get_one::<PathBuf>("config");

                unformat_script(
                    script_path,
                    output_path.map(PathBuf::as_path),
                    config_path.map(PathBuf::as_path),
                    encoding,
                )?;
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

                let stack = export_matches
                    .get_one::<String>("stack-cluts")
                    .and_then(|s| match s.as_str() {
                        "h" | "horizontal" => Some(StackDirection::Horizontal),
                        "v" | "vertical" => Some(StackDirection::Vertical),
                        _ => None,
                    });

                export_texture(texture_path, output_path, format, indexes, cluts, stack)?;
            }
            _ => unreachable!(),
        },
        Some(("debug", _)) => {
            run_debugger()?;
        }
        Some(("autosplitter", autosplitter_matches)) => {
            let live_split_port = *autosplitter_matches
                .get_one::<u16>("live-split-port")
                .expect("live-split-port has a default value");

            let update_frequency = *autosplitter_matches
                .get_one::<u64>("update-frequency")
                .expect("update-frequency has a default value");

            let ending = autosplitter_matches.get_one::<u8>("ending").copied();

            let new_game_plus = autosplitter_matches
                .get_one::<String>("new-game")
                .map(|value| matches!(value.as_str(), "ng+" | "new-game-plus"));

            let log_level = LevelFilter::from_str(
                autosplitter_matches
                    .get_one::<String>("log-level")
                    .expect("log-level has a default value"),
            )
            .unwrap_or(LevelFilter::Info);

            run_autosplitter(
                live_split_port,
                update_frequency,
                ending,
                new_game_plus,
                log_level,
            )?;
        }
        Some(("splits", splits_matches)) => {
            let skip_existing = splits_matches.get_flag("skip-existing");
            let path = splits_matches
                .get_one::<PathBuf>("PATH")
                .expect("Path to splits directory is required");

            create_splits(path, skip_existing)?;
        }
        _ => unreachable!(),
    }

    Ok(())
}
