# Sudoku Prover

This project is based on the idea that you have to prove your deductions to solve a sudoku puzzle.
The framework behind this is written in the Lean Prover language. There are definitions of various constraints as simple as given digits and unique regions (rows, columns, boxes) to theromometers and other stuff.

The goal is to make the proving process as close to normal solving as possible, basically removing the grind of proving while still having the same verification ability. This is difficult, but hopefully there is some middle ground to settle on.

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
*Note: The first time will take a while because it has to download the correct version of lean and mathlib as well as build all of the mathlib library. Future runs of this command will not take as long.*

3. Build the python environment

this will find, download, and build all the python packages required by this project
```bash
uv sync
```

## Run the program

Run the main program with

```bash
uv run sudoku solve -f Puzzles/Framework/4x4FrameworkTest.suko
```

It runs the python file in `sudoku_prover_app/main.py`, meaning you can run it however you like.

The program has a few commands

- `sudoku solve [file]` will run though whatever proof is in the file, then will open up the solving interface and let you solve from there. `--fresh` or `-f` lets you start with an empty proof. `--continue` or `-c` is default.

- `sudoku verify [file]` will run through the proof to check if the proof is complete and correct. Once there are many puzzles with many constraints, this will be used as a testing system.

- `sudoku edit [file]` will open up the editor and allow you to create a puzzle. It is not implemented yet. It will allow for the placement of cells on a grid and be able to add constraints through drawing or selecting. `--blank` or `-b` starts from a blank puzzle with no cells (no file input needed), `--template` or `-t` starts from the given template file, useful if you want to add on top of an existing 9x9 normal sudoku rules apply puzzle.

## Implemented constraints

Generally, unique regions (rows, columns, boxes) are implemented in both Lean and python.

Thermometers are implemented only in Lean.


## Contributing

This project is sort of meant to be my project and I have no expectation that others contribute; however, if you are as invested as I am (or was) to have a go at this, go for it. Want to spruce up the UI? Please do. Want to improve the error handling? I would love it. Want to implement x wings and other fish theorems? Have fun. Want to write some docs on how to use the tools or add to the tools? You are awesome. Want to make a large refactor? Just let me know before you put in a whole bunch of effort. Want to leave things in unfinished states? As long as there are errors saying not implemented, I'm happy at this point.

I am new to keeping things organized on Git or GitHub, so main branches may change at any time without warning. if you are not sure to send in your work, me too. Just start with an issue and we can go from there.

### Adding new constraints

If you want to add a new constraint, there are many steps to implement. First is to create suitable definitions and theorems in Lean. The following definition is just about as simple as it gets. It says that the digit in cell x is less than the digit in cell y

```lean
def LessThan {α} [LT α] (f: Nat -> α) (x y: Nat) := f x < f y
```

Then you need theorems to show that cell x can't be some digit d because reason LessThan.because. Try solve some puzzles with your constraint to get a feeling of how it gets used, in what ways do you eliminate digits from cells.

Then you need to teach python how to use those theorems. Which does not have a fleshed out process in this repo yet.

Any constraint that requires something else besides grid cells to be solved—I'm thinking about global sum (all cages sum to the same value), drawing paths, or creating regions—require extra file fields, extra variables that are in the solution set that the python code is nowhere near ready to handle yet. As an exercise, try taking a sudoku puzzle and prove it all in lean...by hand, that's where I started.



## License & Acknowledgments
This project is licensed under the Apache License 2.0. This repository imports and builds upon the following open-source libraries:
- **Lean 4** & **Mathlib4** – The foundation for formal verification and mathematics (Apache License 2.0). 
- **leanclient** - Python interface for the Lean LSP server (MIT License).
- **Python Arcade** – Powering the visual engine (MIT License).
- **Lark Parser** – Used for parsing logic and syntax (MIT License).

Compliance Note: This project follows the attribution requirements of the Apache 2.0 and MIT licenses for all imported dependencies.
