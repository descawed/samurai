use encoding_rs::*;

fn start_line(
    line_start: &mut bool,
    s: &mut String,
    indentation_level: i32,
    tab_width: Option<usize>,
) {
    if *line_start {
        s.push('\n');
        for _ in 0..indentation_level {
            if let Some(num_spaces) = tab_width {
                for _ in 0..num_spaces {
                    s.push(' ');
                }
            } else {
                s.push('\t');
            }
        }
        *line_start = false;
    }
}

/// Format a script for readability.
///
/// Converts the script from Shift JIS to UTF-8 and adds newlines and indentation at appropriate points.
///
/// # Arguments
///
/// * `script` - The Shift JIS-encoded script text
/// * `tab_width` - If None, the script will be indented with tabs. Otherwise, it will be indented with
///   this many spaces per indentation level.
///
/// # Returns
///
/// The formatted script as a UTF-8 string.
pub fn format_script(script: &[u8], tab_width: Option<usize>) -> String {
    let text = SHIFT_JIS.decode(script).0;
    let mut output = String::with_capacity(text.len());

    let mut in_string = false;
    let mut line_start = false;
    let mut block_start = false;
    let mut indentation_level = 0;
    // skip whitespace at the beginning of the file
    for c in text.chars().skip_while(|c| matches!(c, ' ' | '\t' | '\n')) {
        match c {
            '"' => {
                start_line(&mut line_start, &mut output, indentation_level, tab_width);

                in_string = !in_string; // FIXME: do the scripts allow escapes?
                output.push('"');
                block_start = false;
            }
            ';' if !in_string => {
                start_line(&mut line_start, &mut output, indentation_level, tab_width);

                output.push(';');
                line_start = true;
                block_start = false;
            }
            '{' if !in_string => {
                start_line(&mut line_start, &mut output, indentation_level, tab_width);

                output.push('{');
                line_start = true;
                block_start = true;
                indentation_level += 1;
            }
            '}' if !in_string => {
                indentation_level -= 1;
                // don't start a new line if the block is empty
                if block_start {
                    output.push(' ');
                } else {
                    start_line(&mut line_start, &mut output, indentation_level, tab_width);
                }
                output.push('}');
                line_start = false;
                block_start = false;
            }
            ' ' | '\t' | '\n' if !in_string => {
                if !line_start {
                    output.push(c);
                }
            }
            _ if !in_string && line_start => {
                start_line(&mut line_start, &mut output, indentation_level, tab_width);
                output.push(c);
                block_start = false;
            }
            _ => {
                output.push(c);
                block_start = false;
            }
        }
    }

    output
}

/// Minify a previously-formatted script for storage in volume.dat.
///
/// Converts the script from UTF-8 to Shift JIS, removes newlines and indentation, and collapses whitespace.
///
/// # Arguments
///
/// * `script` - The formatted script text as a UTF-8 string
///
/// # Returns
///
/// The minified script encoded in Shift JIS
pub fn unformat_script(script: &str) -> Vec<u8> {
    let mut minified = String::with_capacity(script.len());
    let mut in_string = false;
    let mut in_space = false;
    for c in script.chars() {
        match c {
            '"' => {
                minified.push('"');
                in_string = !in_string;
                in_space = false;
            }
            ' ' | '\t' | '\n' if !in_string => {
                if !in_space {
                    minified.push(' ');
                    in_space = true;
                }
            }
            _ => {
                minified.push(c);
                in_space = false;
            }
        }
    }

    SHIFT_JIS.encode(&minified).0.to_vec()
}
