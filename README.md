# vhdllint

VHDL linter tool based on cpplint

This is a simple checker and is not guaranteed to be perfect. 
There will be false positives and false negatives. The checker 
will work best on properly formatted VHDL since it operates in 
a line-by-line fashion.

# Installation with PIP

This will make `vhdllint` executable from the local directory and allow it to be modified later.

`pip install -e .`

The tool can now be referenced directly with 

`vhdllint.py ...`

## Usage
Run with:

  `$ vhdllint [OPTIONS] files`

For full usage instructions, run:

  `$ vhdllint --help`

# Rules

- Generics should always be upper case
- Constants should always be upper case
- Non-constant identifiers should always be lower case
- Enumerated type values should always be upper case
- Inconsistent capitalization on identifiers
- Redundant boolean equality checks
- Only one signal/port declaration per line
- Use (others=>'0') instead of x"000"
- Check for file header comment
- Check for copyright notice in header
- File name must include entity name
- Time units should contain a space, e.g. '10 ns' instead of '10ns'
- Space between '--' and comment
- No trailing whitespace
- Newline at the end of the file
- Maximum line length
- Prefer '\n' over '\r\n' for newlines
- Prefer spaces over tabs for indentation
- Indentation should be 2 spaces
- Formatting of TODO comments
- Enforce that positional port mapping is not used
- Check for non standard libraries like std_logic_arith, std_logic_signed, and std_logic_unsigned
- Check for variable use. Variables are often misused
- Check sensitivity list for missing signals
- Check sensitivity list for superfluous signals
- Check sensitivity list for duplicate signals
- Find unused signals, ports, or generics
- Enforce that entity ports to be std_logic or std_logic_vector
- Enforce that port types are only in, out, or inout
- Simulation loops must have a wait statement
- Use rising/falling_edge instead of clk'event
- Check for multiple drivers on a signal
- Check that integer types have a range specified, otherwise 32-bit is used.
- Check for inferred latches with "when...else"
- Check for combinational loops in non clocked processes
- Check for too many blank lines in a row
- Prefer direct instantiation over component declaration
- Generics should have prefix G_
- Constants should have prefix C_
- FSM state types should have prefix ST_ or suffix _ST
- Clocks should have suffix _clk
- Check for local variables shadowing signals
- Check for redundant state assignments in registered FSM
- Check for arithmetic expressions in if statements
- Check for VHDL2008 'process(all)' construct
- Check for VHDL2008 'boolean style' conditional operator for non-boolean types
- Check for blank lines around major blocks (entity, architecture, package,
  package body)
- Check for VHDL2008 reading of output ports

# vhdltidy.sh

Helper script to automate fixing some simple whitespace / formatting issues

Run with:

  `$ sh vhdltidy.sh list_of_vhdl_files`

Example:

`$ shopt -s globstar` # for enabling recursive **  
`$ sh vhdltidy.sh project/**/*.vhd`

# Integration with VSCode

This will allow vhdllint to run on save and add entries to the problems log.

Add the following to `tasks.json`.

```
{
    "label": "vhdllint",
    "type": "shell",
    "windows": {
                "command": "vhdllint",
                "args": ["'${file}'"]
    },
    "presentation" :{
        "reveal": "never"
    },
    "problemMatcher": [
        // items with severity 4-5 as error
        {
            "owner": "external",
            "fileLocation": ["absolute"],
            "severity": "error",
            "pattern": {
            "regexp": "^(.*):(\\d+):\\[(\\d+),(\\d+)\\]:\\s+(.*)\\s+\\[(.*)\\]\\s+\\[[4-5]\\]$",
            "file": 1,
            "line": 2,
            "column" : 3,
            "endColumn" : 4,
            "message": 5,
            }
        },
        // items with severity 1-3 as warning
        {
            "owner": "external",
            "fileLocation": ["absolute"],
            "severity": "warning",
            "pattern": {
            "regexp": "^(.*):(\\d+):\\[(\\d+),(\\d+)\\]:\\s+(.*)\\s+\\[(.*)\\]\\s+\\[[1-3]\\]$",
            "file": 1,
            "line": 2,
            "column" : 3,
            "endColumn" : 4,
            "message": 5,
            }
        },
        // items with severity 0 as info
        {
            "owner": "external",
            "fileLocation": ["absolute"],
            "severity": "info",
            "pattern": {
            "regexp": "^(.*):(\\d+):\\[(\\d+),(\\d+)\\]:\\s+(.*)\\s+\\[(.*)\\]\\s+\\[[0]\\]$",
            "file": 1,
            "line": 2,
            "column" : 3,
            "endColumn" : 4,
            "message": 5,
            }
        }
    ]
}

```

Add the following to `keybindings.json`

```
{
    "key": "ctrl+s",
    "command": "workbench.action.tasks.runTask",
    "args": "vhdllint",
    "when": "editorLangId == vhdl"
}
```