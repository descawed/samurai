use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Result};
use clap::{arg, Command};

use samurai::load_volume;

fn cli() -> Command {
    Command::new("samurai")
        .about("Manipulate files for the PS2 game (Way of the) Samurai")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .subcommand(
            Command::new("volume")
                .about("Pack or unpack volume.dat")
                .arg(arg!(<PATH> "Path to volume.dat").value_parser(clap::value_parser!(PathBuf)))
                .subcommand(Command::new("list").about("List contents of volume.dat"))
                .subcommand(
                    Command::new("unpack")
                        .about("Unpack the contents of volume.dat")
                        .arg(
                            arg!(<PATH> "Path to a directory where the volume will be extracted")
                                .value_parser(clap::value_parser!(PathBuf)),
                        ),
                ),
        )
}

fn list_volume(path: &Path) -> Result<()> {
    let volume = load_volume(path)?;
    let mut names: Vec<_> = volume.iter().map(|(n, _)| n).collect();
    names.sort();

    for name in names {
        println!("{}", name);
    }

    Ok(())
}

fn unpack_volume(volume_path: &Path, extract_path: &Path) -> Result<()> {
    if extract_path.is_file() {
        return Err(anyhow!("Unpack path must be a directory"));
    }

    if !extract_path.exists() {
        fs::create_dir(extract_path)?;
    }

    let volume = load_volume(volume_path)?;
    for (name, data) in volume.iter() {
        let mut output_path = extract_path.to_path_buf();
        for dir in name.split(&['/', '\\']) {
            output_path = output_path.join(dir);
        }

        if let Some(parent) = output_path.parent() {
            if !parent.exists() {
                fs::create_dir_all(parent)?;
            }
        }

        fs::write(&output_path, data)?;
    }

    Ok(())
}

fn main() -> Result<()> {
    let matches = cli().get_matches();

    match matches.subcommand() {
        Some(("volume", sub_matches)) => {
            let volume_path = sub_matches
                .get_one::<PathBuf>("PATH")
                .expect("Path to volume.dat is required");

            match sub_matches.subcommand() {
                Some(("list", _)) => list_volume(volume_path)?,
                Some(("unpack", unpack_matches)) => {
                    let extract_path = unpack_matches
                        .get_one::<PathBuf>("PATH")
                        .expect("Path to extraction directory is required");
                    unpack_volume(volume_path, extract_path)?;
                }
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }

    Ok(())
}
