# samurai

Tools for working with the files of the game (Way of the) Samurai (2002). These have currently only been tested on the original Japanese release.

## Usage

Build with `cargo build`. All the tools are contained in a single binary called `samurai`. The following subcommands are currently provided; use the `help` subcommand or `-h`/`--help` option for details.

- `samurai volume` - List, unpack, or pack volume.dat.
- `samurai script` - Convert and format script files for easier reading. Can also (loosely) reverse the process when you're ready to store them back in volume.dat.

## Scripts

Game scripts are in the `script` folder in volume.dat. They're plain text, although they use the Shift JIS encoding and are all on one line. Use `samurai script format` to convert to UTF-8 and apply some
basic formatting. The syntax is still a bit of a mystery to me, but here's what I've been able to discern so far:

- Variables and definitions usually start with `#`
- Function calls usually start with `$`
- All statements end with `;`, including the closing `}` of blocks (for if/elseif/else statements, only the final block ends with a `;`)
- Definitions/assignments consist of a variable name, followed by either `|`, `:`, or `=`, followed by the value. I'm not currently sure what the difference between the 3 operators is.
- Function definitions start with `?F`, optionally followed by an argument list in parentheses (no `#` in front of the argument names), followed by the function body in `{}`
- Return early from a function with `/return;`
- If statements start with `?i`, followed by a condition in parentheses, followed by a `{}` block
- For elseif, instead of ending the if block with `;`, follow it with another condition in parentheses and another `{}` block. This can be repeated as many times as needed.
- For else, follow the last if/elseif block immediately with another `{}` block. There's no keyword or anything.
