# this is the main file that the cli interacts with
# should have options for solve, edit, verify, edit from template, anything really

import argparse
from typing import List

from sudoku_prover_ui.proof_engine import ProofEngine
from sudoku_prover_ui.puzzle import Puzzle


def solve(args: List[str]):
    if not args:
        print('solve expects an option or file')
    
    

    if len(args) != 2:
        print('please give a .suko file to use as input')
        exit(1)

    with open(args[1],'r') as f:
        text = f.read()

    parts = text.split("PROOF", 1)
    definition_text = parts[0]
    proof_text = (parts[1].strip() if len(parts) > 1 else "").splitlines()

    puzzle = Puzzle.import_puzzle(definition_text,args[1])
    
    print('starting up Lean Server',end=' ')
    engine = ProofEngine(puzzle)
    print('done')

    # run through proof steps
    for line in proof_text:
        engine.command(line)


    print('starting up the UI')
    from sudoku_prover_ui import solver_ui # This keeps arcade from trying to run for other commands like verify
    solver_ui.main(puzzle, engine)


def verify(args: List[str]):
    # verifies the proof of a suko file
    if not args:
        print('no file given to verify')
        exit(1)
    file_name = args.pop(0)


def edit(file_name: str, start_blank: bool, template: bool):
    if start_blank:
        # edit from blank
        pass
    elif file_name:
        # edit from file
        pass
    else:
        print('No file given to edit or blank option not set')
        exit(1)
    raise NotImplementedError('edit mode not implemented yet')


def main():
    parser = argparse.ArgumentParser(description="Solve sudokus")
    subparsers = parser.add_subparsers(dest="command", help="Available commands",required=True)
    # solve
    solve_parser = subparsers.add_parser("solve", help="Open the UI and solve the puzzle")
    solve_parser.add_argument("file", help="Path to puzzle file")
    group = solve_parser.add_mutually_exclusive_group()
    group.add_argument("-c","--continue",action="store_true",dest="cont",default=True,help="Continue from end of the proof text (Default)")
    group.add_argument("-f","--fresh",action="store_false",dest="cont",help="Start the proof from the beginning")
    # verify
    verify_parser = subparsers.add_parser("verify",help="Check the proof text of the puzzle")
    verify_parser.add_argument("file",help="Path to puzzle file")
    # edit
    edit_parser = subparsers.add_parser("edit",help="edit or create a puzzle")
    edit_parser.add_argument("file",nargs='?',help="file to edit")
    edit_parser.add_argument("-t","--template",action="store_true",help="Start from a template")
    edit_parser.add_argument("-b","--blank",action="store_true",help="Start from blank")


    args = parser.parse_args()
    if args.command == 'solve':
        solve(args.file,args.cont)
    elif args.command == 'verify':
        verify(args.file)
    elif args.command == 'edit':
        edit(args.file,agrs.blank,args.template)



if __name__ == '__main__':
    main()
