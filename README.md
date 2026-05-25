# samurai

Tools for working with the files of the game (Way of the) Samurai (2002).

## Usage

Build with `cargo build`. All the tools are contained in a single binary called `samurai`. The following subcommands are
currently provided; use the `help` subcommand or `-h`/`--help` option for details.

- `samurai volume` - List, unpack, or pack volume.dat.
- `samurai module` - Unpack or pack MODULE.BIN (not present in the original Japanese release).
- `samurai texture` - List information about game textures and convert them to other formats.
- `samurai script` - Convert and format script files for easier reading. Can also (loosely) reverse the process when
  you're ready to store them back in volume.dat.
- `samurai debug` - Debug the game running in PCSX2.

## Scripts

Game scripts are in the `script` folder in volume.dat. They're plain text, although they use the Shift JIS encoding and
are all on one line. Use `samurai script format` to convert to UTF-8 and apply formatting. You can also point this
command to the game's `config.h` to have it replace literals with symbolic constants. Due to the parsing library used,
this tool's parser is stricter than the game's own parser and a few scripts will fail to parse. You can use the
`--simple` flag to apply only basic formatting without using the full parser, or edit the script to "correct" the syntax
prior to formatting. Specifically, the only script currently failing is p01/e21/e21.sol, which you can fix by changing
the line `$Flag_Fukki = 1` to `$#Flag_Fukki = 1`.

The `script` directory in this repo contains some utilities for working with scripts. The `vscode-extension` directory
contains a VS Code extension providing syntax highlighting for this language. `format-scripts.sh` is a shell script
which can be used to batch-format all the game's scripts. It takes two arguments: an input directory, which should be
the path to the game's `script` directory, and an output directory where the formatted scripts will be written.

### Syntax

"Samurai script" is an object-oriented, interpreted scripting language. The general syntax is:

- A sequence of digits forms an integer literal: `123`
- A sequence of digits, followed by a period, followed by a sequence of digits, forms a float literal: `123.456`
- Numeric literals may also start with a minus sign for negative numbers: `-123`/`-123.456`. The minus sign is
  considered part of the literal, not an operator.
- Text enclosed in double quotes forms a string literal: `"abcd"`. The escape sequence `\n` is supported to indicate
  a newline. I'm not sure if it's possible to escape quotes as I haven't seen any examples of strings that include a
  quote character.
- Comments start with `//` and extend to the end of the line. The script formatter does not currently support comments.
- Variables generally start with `#` (`#MyVariable`) while function names are generally bare identifiers (`MyFunc`).
  This is not a hard requirement, though – variables may omit the `#` prefix and functions may include it.
- Both variable and function names may be prefixed with `$` to search for or define them in the global scope:
  `$#MyGlobalVariable`, `$MyGlobalFunc`. This doesn't actually seem to _require_ the name to be in the global scope;
  rather, I believe it inverts the search order, so instead of looking for the name in the current scope and recursively
  walking up if it isn't found, the search will instead start from the global scope and recursively search down if it
  isn't found. As a consequence, the `$` prefix is optional as long as the global value's name isn't shadowed by another
  variable in an inner scope, and there are a few globals where scripts generally omit the `$` by convention (the global
  variable `#object` and the built-in functions `not` and `list`).
- `:` is used to define a variable by value, i.e. by making a copy of the value on the right: `#MyVar : 4`
- `|` is used to define a variable by reference, i.e. the variable on the left will be a reference to the value on
  the right: `#MyVar | #SomeObj`
- Variable definitions are expressions; e.g., something like the following is legal: `(#MyVar : 4) add 1`
- Statements end with `;`: `#MyVar | #SomeObj;`. However, the semicolon is optional if the statement is the last one in
  the block. Empty statements (a lone `;`) are allowed.
- Function calls consist of the function name optionally followed by a comma-delimited list of argument expressions:
  ```
  MyFunc 1, 2;
  FuncNoArgs;
  ```
- Method calls consist of the object variable, followed by the method name as a bare identifier, followed by an optional
  argument list as described above for function calls: `#Object method #argument1, #argument2;`
- A variable name immediately following another variable name is treated as a non-method attribute access, e.g.
  `#Object#Attribute`. This can be nested indefinitely for attributes which have their own attributes, e.g.
  `#Object#SubObject#SubSubObject#Attribute`.
- Function and method calls are expressions and their result may be assigned to a variable:
  `#IsPlayerDead | $GetCharDead $#CHID_SHUJINKO;`
- Function definitions start with `?F`, optionally followed by an argument list in parentheses (typically with no `#` in
  front of the argument names, although it is allowed), followed by the function body in `{}`. This is an expression and
  can be assigned to a variable, which is how functions are usually defined. Usually, the `#` prefix is used on the
  variable when defining the function but not when calling it:
  ```
  #MyFunc | ?F (a, b, c) {
    #LocalVar : #a;
  };
  MyFunc 1, 2, 3;
  ```
  Note that a small number of scripts have function definitions which omit the `?F`, or have only a `?` with no `F`.
  The formatter will parse these and format them with the full `?F` keyword, but I think these may actually be sytnax
  errors that don't parse correctly in the game. Further investigation is needed.
- Consecutive commas in argument lists are coalesced. For example, `f 1, , 2` parses as two arguments.
- If statements start with `?i`, followed by a condition in parentheses, followed by a `{}` block:
  ```
  ?i (#a eq #b) {
    $Print "a is equal to b";
  };
  ```
  Note that, as this is a statement, the block ends with a semicolon `;`.
- For elseif, instead of ending the if block with `;`, follow it with another condition in parentheses and another `{}`
  block. This can be repeated as many times as needed.
  ```
  ?i (#a eq #b) {
    $Print "a is equal to b";
  } (#a eq #c) {
    $Print "a is equal to c";
  };
  ```
- For else, follow the last if/elseif block immediately with another `{}` block; there's no keyword or anything:
  ```
  ?i (#a eq #b) {
    $Print "a is equal to b";
  } (#a eq #c) {
    $Print "a is equal to c";
  } {
    $Print "a is not equal to b or c";
  };
  ```
- Return early from a function with `/return;`:
  ```
  ?F (a) {
    ?i (#a eq 0) {
      /return;
    };
    DoStuff #a;
  }
  ```
  In fact, only the `/r` portion of the keyword is significant. The text following the `r` can be anything or nothing -
  `/r`, `/return`, `/rfoo`, etc.

  Note that although built-in functions can return values, there is no syntax for a user-defined function to return a
  value. If you need to return a value, you'll have to store it in a global variable that the caller can check.
- While loops are introduced with the `?W` keyword, followed by a block containing a condition in parentheses, followed
  by a comma, followed by a block containing the loop body:
  ```
  #iii : 75;
  ?W { (#iii le 84) }, {
    $AIDeleteCharacter #iii;
    #iii add 1;
  };
  ```
- Break out of a loop with `/break;`:
  ```
  ?W { ($#StrCount ge 0) }, {
    ?i(($GetCharRange (#SeizonList at $#StrCount), 0, $#Dist) eq 1){
      /break;
    };
    #StrCount sub 1;
  };
  ```
  Like the `/return` keyword, only the `/b` portion of the keyword is significant.
- The language supports a `?I` keyword for ternary conditional expressions: `?I #condition, #true_value, #false_value`.
  No scripts have been observed to use this syntax, but the built-in `not` function is internally defined as a macro
  which expands to `?I (#condition), 0, 1`.
- Object attributes are defined via the `@` operator. The left-hand side of the operator is the object to add the
  attributes to and the right-hand side is a block `{}`. This is a normal code block that can contain any arbitrary
  statements, but any variables defined in this block become attributes/methods of the object:
  ```
  (#ClassFLAG : #object) @{
    #id : $#CHID_SHUJINKO;
    #SET : ?F (a) {
        #id = #a;
    };
  };
  ```
  There is no `this` or `self` variable in methods; non-global variable references which are not found in the local
  scope are implicitly looked up on the receiver.
- Beyond `@`, there are no operators to speak of. All other comparison and manipulation of objects is done via methods.
  Even `=` is not an operator, but rather a method of integers and floats (which also means `=` can't be used to define
  a variable, only change the value of an existing object).

### Types

Everything is an object, but there are a few built-in subtypes with predefined methods.

- Floats provide basic math methods: `add`, `sub`, `mul`, `div`, and `=` to copy the value from another float. All of
  these methods modify the float object in-place, but they also return the object for method chaining. Floats also
  provide comparison methods: `eq`, `lt`, `le`, `gt`, `ge`. `<` and `>` are also available as aliases for `lt` and `gt`.
  There is no boolean type; the result of comparisons is an integer 1 or 0.
- Integers provide all the same methods as floats, but because they pull double-duty as booleans, they also have the
  logical methods `and` and `or`. Note that neither floats nor integers have a `ne` method; instead, use the built-in
  function `not` to invert the result of an `eq` (e.g. `not (#a eq #b)`).
- Strings provide an `add` method for concatenation.
- Arrays can be defined via the built-in function `list`, which takes a variable number of arguments, e.g.
  `(list 1, 2, 3)` (by convention, calls to `list` are wrapped in parentheses). The `at` method is used to index into an
  array.
- Functions are also objects, but they have no methods that I'm aware of.

There's no syntax for user-defined types/classes, but scripts emulate classes by using prototype objects. The global
variable `#object` contains an empty object with no attributes. To define a class, a script will make a by-value copy of
this object and define any desired attributes and methods of the class on the copy:

```
(#ClassFLAG : #object) @{
  #id : $#CHID_SHUJINKO;
  #SET : ?F (a) {
      #id = #a;
  };
};
```

Then the script can create "instances" of this class by making copies of the class object:

```
#FlagSuzu : #ClassFLAG;
#FlagSuzu SET $#CHID_SUZU;
#FlagDona : #ClassFLAG;
#FlagDona SET $#CHID_DONA;
#FlagShire : #ClassFLAG;
#FlagShire SET $#CHID_SHIRETOKO;
```

## Debugger

The debugger allows monitoring the game internals while it runs in PCSX2. It's currently limited to support for the
following:

- Japanese game versions (SLPS-20178 and SLPM-74405)
- Linux only
- Read-only

The `debug` command has no options; it will automatically wait for and attach to a PCSX2 process. Once attached, the
display updates every 3 seconds. Press `q` to exit. The debugger provides a TUI with three sections: Globals,
Characters, and Flags. Use tab to switch between them.

### Globals

The Globals panel displays various global game state variables that may be of interest.

### Characters

The Characters panel displays a list of all characters loaded in the current scene. Each character displays a summary
line with their ID, name, and HP. Select a character with the arrow keys and press enter to toggle a detail view with
additional information.

### Flags

The Flags panel displays global flags and variables that scripts use to track progression and event state. There are
four tabs corresponding to the four flag/variable types:

- **Man** - event manager flags; corresponds to script functions `SetEventManFlag` and `GetEventManFlag`
- **Pro** - event progress flags; corresponds to `SetEventProFlag` and `GetEventProFlag`
- **Int**- integer variables; corresponds to `SetVarInt` and `GetVarInt`
- **Act** - event act end flags; corresponds to `SetEventActEndFlag` and `GetEventActEndFlag`

Use the left and right arrow keys to switch between tabs and the up and down arrow keys to scroll through the flags.
Flags whose value is 0 (the default value) are grayed out to make flags that have been set stand out.