## Suko File Format

The suko file format is meant to be a human readable format that stores puzzle information and proof information.

Suko files can import a collection of predefined constraints for puzzles that use very similar constraints like normal 9x9 sudoku grid

If you like reading the grammar, see suko.lark

Suko file is made up of several sections denoted with all caps headers. The sections must be in order, but not all sections are required. Most of the file is key value pairs of the form `key value` seperated by new lines. If value is a string, it must be enclosed in double quotes `key "value"`

The sections are
- TEMPLATE?
- METADATA?
- DEFINITION
- PROOF?

### TEMPLATE

The template section is only for template files. Being the first line in the file, it signifies to the parser that it is a template file. Template files are not required to fill all the definition fields, and must not have a proof section
Template section contains two fields:
- `lean_source`, the file path to the lean file where it is defined
- `lean_code`, how it should be used by other files like 'NormalSudoku f'

### METADATA

This section lets you put any data about the puzzle you wish. Currently the section is not required. Any keys are allowed, values must be strings. If the file is a template, currently the name field is required. Example things to store in metadata:

```
METADATA
name "puzzle name"
author "me"
link "a link to the internet"
description "this is an motivation of the puzzle"
```

### DEFINITION

The main section, required by all files. Contains the following key value pairs:
- `cell_count`, an integer 0 or greater, tells how many cells are in the puzzle
- `cell_layout`, a list of tuples telling the UI how the cells are arranged
- `symbols`, a string. Expects to find a lean file by the same name with that definition in it. Note that these fields are not required in the file, but they are required to be in at least one file that is under imported constraints or the file itself

#### constraints

`constraints` and `imported_constraints` are subsections. Each key value pair in these sections must have a dash before it so that the parser can find the end of the subsection. `imported_constraints` are key value pairs where the value is a the path to a template suko file where that imported constraint is defined. A template is allowed to import other templates. If the `cell_count`, `cell_layout`, and `symbols` are defined in more than one file, they must match. `constraints` are key value pairs where the value is the actual lean code that defines it. The name of the constraints can be anything as long as they are unique.

example imported constraint section
```
imported_constraints
- base "Puzzles/NormalSudoku.suko"
```
example constraints section
```
constraints
- given15 "f 15 = 2"
- given20 "f 20 = 4"
```

### PROOF

This section contains the proof or an incomplete proof of a puzzle. Templates must not contain this section. The proof is lines of commands that can be understood by the proof engine. The hope is that these are in a condensed enough form that they are roughly readable, while also being very accurate in what they do. If the proof section is missing or empty, there is no proof yet.

There is no designation in the file that a proof is complete, the sudoku verify command can check that the proof is correct.
