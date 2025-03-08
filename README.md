# samurai

Tools for working with the files of the game (Way of the) Samurai (2002). These have currently only been tested on the
original Japanese release.

## Usage

Build with `cargo build`. All the tools are contained in a single binary called `samurai`. The following subcommands are
currently provided; use the `help` subcommand or `-h`/`--help` option for details.

- `samurai volume` - List, unpack, or pack volume.dat.
- `samurai script` - Convert and format script files for easier reading. Can also (loosely) reverse the process when
  you're ready to store them back in volume.dat.

## Scripts

Game scripts are in the `script` folder in volume.dat. They're plain text, although they use the Shift JIS encoding and
are all on one line. Use `samurai script format` to convert to UTF-8 and apply formatting. You can also point this
command to the game's `config.h` to have it replace literals with symbolic constants. Due to the parsing library used,
this tool's parser is stricter than the game's own parser and a few scripts will fail to parse. You can use the
`--simple` flag to apply only basic formatting without using the full parser, or edit the script to "correct" the syntax
prior to formatting.

### Syntax

"Samurai script" is an object-oriented, interpreted scripting language. The general syntax is:

- A sequence of digits forms an integer literal: `123`
- A sequence of digits, followed by a period, followed by a sequence of digits, forms a float literal: `123.456`
- Text enclosed in double quotes forms a string literal: `"abcd"`. The escape sequence `\n` is supported to indicate
  a newline. I'm not sure if it's possible to escape quotes as I haven't seen any examples of strings that include a
  quote character.
- Variables generally start with `#`: `#MyVariable`
- Function names are generally bare identifiers: `MyFunc`
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
- All statements end with `;`: `#MyVar | #SomeObj;`
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
- Function definitions start with `?F`, optionally followed by an argument list in parentheses (no `#` in front of the
  argument names), followed by the function body in `{}`. This is an expression and can be assigned to a variable, which
  is how functions are usually defined. Usually, the `#` prefix is used on the variable when defining the function but
  not when calling it:
  ```
  #MyFunc | ?F (a, b, c) {
    #LocalVar : #a;
  };
  MyFunc 1, 2, 3;
  ```
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
  Note that although built-in functions can return values, there is no syntax for a user-defined function to return a
  value. If you need to return a value, you'll have to store it in a global variable that the caller can check.
- Object attributes are defined via the `@` operator. The left-hand side of the operator is the object to add the
  attributes to and the right-hand side is a block `{}`. This is a normal code block which can contain any arbitrary
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
  provide comparison methods: `eq`, `lt`, `le`, `gt`, `ge`. There is no boolean type; the result of comparisons is an
  integer 1 or 0.
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