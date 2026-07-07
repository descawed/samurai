use std::borrow::Cow;
use std::fs;
use std::io::Write;
use std::path::Path;

use encoding_rs::{SHIFT_JIS, WINDOWS_1252};
use strum::EnumString;

use crate::script;
use crate::script::ScriptFormatter;

#[derive(Clone, Copy, Debug, EnumString)]
pub enum Encoding {
    #[strum(serialize = "utf-8")]
    Utf8,
    #[strum(serialize = "shift-jis")]
    ShiftJis,
    #[strum(serialize = "windows-1252")]
    Windows1252,
    #[strum(serialize = "detect")]
    Detect,
}

impl Encoding {
    fn convert_from<'a>(&self, raw: &'a [u8]) -> Cow<'a, str> {
        match self {
            Self::Utf8 => String::from_utf8_lossy(raw),
            Self::ShiftJis => SHIFT_JIS.decode(raw).0,
            Self::Windows1252 => WINDOWS_1252.decode(raw).0,
            Self::Detect => {
                let label = chardet::detect(raw).0;
                let encoding = encoding_rs::Encoding::for_label(label.as_bytes()).unwrap();
                encoding.decode(raw).0
            }
        }
    }

    fn convert_to<'a>(&self, text: &'a str) -> Cow<'a, [u8]> {
        match self {
            Self::Utf8 => Cow::Borrowed(text.as_bytes()),
            Self::ShiftJis => SHIFT_JIS.encode(text).0,
            Self::Windows1252 => WINDOWS_1252.encode(text).0,
            Self::Detect => panic!("Can't detect to-encoding"),
        }
    }
}

pub fn format_script(
    script_path: &Path,
    output_path: Option<&Path>,
    tab_width: Option<usize>,
    use_simple_parser: bool,
    config_path: Option<&Path>,
    encoding: Encoding,
    quiet: bool,
) -> anyhow::Result<()> {
    let raw = fs::read(script_path)?;
    let text = encoding.convert_from(&raw);

    let formatted = if use_simple_parser {
        script::format_script(text, tab_width)
    } else {
        let mut formatter = ScriptFormatter::new();
        formatter.set_quiet(quiet);
        if let Some(path) = config_path {
            let config_text = fs::read_to_string(path)?;
            formatter.use_config(&config_text)?;
        }
        formatter.format_script(text, tab_width)?
    };

    if let Some(output_path) = output_path {
        fs::write(output_path, formatted)?;
    } else {
        print!("{}", formatted);
    }

    Ok(())
}

pub fn unformat_script(
    script_path: &Path,
    output_path: Option<&Path>,
    config_path: Option<&Path>,
    encoding: Encoding,
    obfuscate: bool,
) -> anyhow::Result<()> {
    let mut formatter = ScriptFormatter::new();
    formatter.set_obfuscate(obfuscate);
    if let Some(path) = config_path {
        let config_text = fs::read_to_string(path)?;
        formatter.use_config(&config_text)?;
    }
    let text = formatter.unformat_script(&fs::read_to_string(script_path)?)?;
    let raw = encoding.convert_to(&text);
    if let Some(output_path) = output_path {
        fs::write(output_path, raw)?;
    } else {
        std::io::stdout().write_all(&raw)?;
    }

    Ok(())
}
