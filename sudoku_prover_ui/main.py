# this is the main file that the cli interacts with
# should have options for solve, edit, verify, edit from template, anything really

import argparse
import os

from sudoku_prover_ui.proof_engine import ProofEngine
from sudoku_prover_ui.puzzle import Puzzle


def import_file(file_name: str,is_puzzle: bool = True):
    # check if it exists
    if not os.path.exists(file_name):
        print(f"File '{file_name}' could not be found")
        exit(1)
    # check if it is a directory
    if not os.path.isfile(file_name):
        print(f"'{file_name}' is a directory")
        exit(1)
    # get the text
    try:
        with open(file_name,'r') as f:
            text = f.read()
    except PermissionError:
        print(f"You do not have permission to read '{file_name}'")
        exit(1)
    # process it
    parts = text.split("PROOF", 1)
    definition_text = parts[0]
    proof_text = (parts[1].strip() if len(parts) > 1 else "").splitlines()

    puzzle = Puzzle.import_puzzle(definition_text,file_name,is_puzzle)

    return (puzzle,proof_text)

def solve(file_name: str, cont: bool):
    
    puzzle, proof_text = import_file(file_name)

    print('starting up Lean Server',end=' ',flush=True)
    engine = ProofEngine(puzzle)
    print('done')

    if cont:
        # run through proof steps
        for line in proof_text:
            engine.command(line)

    print('starting up the UI')
    from sudoku_prover_ui import solver_ui # This keeps arcade from trying to run for other commands like verify
    solver_ui.main(puzzle, engine)


def verify(file_name: str):
    # verifies the proof of a suko file
    puzzle, proof_text = import_file(file_name)

    print('starting up Lean Server',end=' ',flush=True)
    engine = ProofEngine(puzzle)
    print('done')

    print('running through the proof')
    for line in proof_text:
        engine.command(line)
    
    if engine.current.count_goals() != 0:
        print("the proof looks incomplete")
        print("ended with the following proof state")
        print(engine.current.grid)
        print(engine.current.proof_state)
        exit(2)

    # proof succeded here, yay
    print('the proof is correct')


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
    opt_file_parser = argparse.ArgumentParser(add_help=False)
    opt_file_parser.add_argument("file",nargs="?",help="The target file")

    req_file_parser = argparse.ArgumentParser(add_help=False)
    req_file_parser.add_argument("file",help="The target file")

    parser = argparse.ArgumentParser(description="Solve sudokus")
    subparsers = parser.add_subparsers(dest="command", help="Available commands",required=True)
    # solve
    solve_parser = subparsers.add_parser("solve", parents=[req_file_parser],help="Open the UI and solve")
    group = solve_parser.add_mutually_exclusive_group()
    group.add_argument("-c","--continue",action="store_true",dest="cont",default=True,help="Continue from end of the proof text (Default)")
    group.add_argument("-f","--fresh",action="store_false",dest="cont",help="Start the proof from the beginning")
    # verify
    verify_parser = subparsers.add_parser("verify",parents=[req_file_parser],help="Check the proof text of the puzzle") # pyright: ignore[reportUnusedVariable]
    # edit
    edit_parser = subparsers.add_parser("edit",parents=[opt_file_parser],help="edit or create a puzzle")
    edit_parser.add_argument("-t","--template",action="store_true",help="Start from a template")
    edit_parser.add_argument("-b","--blank",action="store_true",help="Start from blank (file not required)")


    args = parser.parse_args()
    # change the file to a full path for error reporting
    if args.file:
        args.file = os.path.abspath(args.file)

    if args.command == 'solve':
        solve(args.file,args.cont)
    elif args.command == 'verify':
        verify(args.file)
    elif args.command == 'edit':
        if not args.file and not args.blank:
            edit_parser.error("file or blank is required")
        edit(args.file,args.blank,args.template)


if __name__ == '__main__':
    main()
