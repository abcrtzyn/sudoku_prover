# Sudoku Prover
This projects is based on the idea that you have to prove your deductions to solve a sudoku puzzle.
The framework behind this is written in the Lean Prover language. There are definitions of various constraints as simple as given digits and unique regions (rows, columns, boxes) to theromometers and other stuff.

The goal is to make the solving process is close to normal solving as possible, basically removing the grind of proving while still having the same verification ability. This is difficult, but hopefully there is some middle ground to settle on.

## Build the environment
0. Install the following tools
    - **lean**: follow instructions at the [lean install site](https://lean-lang.org/install/). The VS Code extension install was easiest for my workflow.
    - **uv** package manager: follow instructions at [uv getting started docs](https://docs.astral.sh/uv/getting-started/installation/). I did the standalone method. uv is required for the PyPantograph package.

1. Clone this repo
2. Build the lean environment

this will build all the definitions and proofs of all the constraints
```bash
lake build
```
*Note: The first time will take a while because it has to download the correct version of lean and mathlib as well as build all of the mathlib library. Future runs of this command will not take as long*

3. Build the python environment

this will find, download, and build all the python packages required by this project
```bash
uv sync
```

4. Once the environment is setup, run using
```bash
uv run sudoku solve -f Puzzles/Framework/4x4FrameworkTest.suko
```

`uv run sudoku` is an alias for `sudoku_prover_ui/main.py` so other options like `uv run python sudoku_prover_ui/main.py solve ...` or `python3 sudoku_prover_ui/main.py solve ...` are just fine too.

The program has a few commands
- `sudoku solve [file]` will run though whatever proof is in the file, then will open up the solving interface and let you solve from there. `--fresh` or `-f` lets you start with an empty proof. `--continue` or `-c` is default.
- `sudoku verify [file]` will run through the proof to check if the proof is complete and correct. Once there are many puzzles with many constraints, this will be used as a testing system.
- `sudoku edit [file]` will open up the editor and allow you to edit where the cells are and add in a constraint to the puzzle. `--blank` or `-b` starts from nothing (no file input needed), `--template` or `-t` starts from the given template file, useful if you want to add on top of an existing 9x9 normal sudoku rules apply. The editor is not implemented yet.

## Project Status
Features are functional at this point
I have no set plan on what gets implemented next
There will be development until I am happy with the state of it, or it has gotten to a point where I feel stuck.

Both unique regions and thermometers are implemented in lean, but thermometers are not implemented in the python code.

## License & Acknowledgments
This project is licensed under the Apache License 2.0. This repository imports and builds upon the following open-source libraries:
- **Lean 4** & **Mathlib4** – The foundation for formal verification and mathematics (Apache License 2.0). 
- **PyPantograph** – Python interface for Lean (Apache License 2.0).
- **Python Arcade** – Powering the visual engine (MIT License).
- **Lark Parser** – Used for parsing logic and syntax (MIT License).

Compliance Note: This project follows the attribution requirements of the Apache 2.0 and MIT licenses for all imported dependencies.
