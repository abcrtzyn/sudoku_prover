# this is the main file that the cli interacts with
# should have options for solve, edit, verify, edit from template, anything really

import sys

from sudoku_prover_ui import solver_ui
from sudoku_prover_ui.proof_engine import ProofEngine
from sudoku_prover_ui.puzzle import Puzzle


def main():
    # step 0 check for command line args
    args = sys.argv
    if len(args) != 2:
        print('please give a .suko file to use as input')

    with open(args[1],'r') as f:
        text = f.read()

    parts = text.split("PROOF", 1)
    definition_text = parts[0]
    proof_text = parts[1].strip() if len(parts) > 1 else ""

    puzzle = Puzzle.import_puzzle(definition_text,args[1])
    
    print('starting up Lean Server',end=' ')
    engine = ProofEngine(puzzle)
    print('done')

    print('starting up the UI')
    solver_ui.main(puzzle, engine)


if __name__ == '__main__':
    main()
