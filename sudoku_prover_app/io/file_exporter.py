"""Take an object from Puzzle class and export it to a suko file"""

import hashlib
from io import TextIOWrapper
from pathlib import Path
from typing import Dict, Iterable
from sudoku_prover_app.io.file_parser import import_file
from sudoku_prover_app.core.puzzle import Puzzle, Template

grammar_file = Path(__file__).resolve().parent.parent.parent.joinpath('suko.lark')

EXPECTED_HASH = "8584c8db" # current version

with open(grammar_file, 'rb') as f:
    current = hashlib.md5(f.read()).hexdigest()[:8]
    if current != EXPECTED_HASH:
        print(f'warning: grammar has been changed, export file may not result in the same format. new hash value {current}')


def write_constraints(f: TextIOWrapper,constraints: Dict[str,str]):
    for name, text in constraints.items():
        f.write(f'- {name} "{text}"\n')



def export_file(filename: str, puzzle: Puzzle | Template, proof: Iterable[str] | None = None):
    proof = proof or []
    is_puzzle = isinstance(puzzle,Puzzle)

    if not is_puzzle and proof:
        raise ValueError('template can not have a proof')
    with open(filename, 'w+') as f:
        if not is_puzzle:
            # template section
            f.write('TEMPLATE\n')
            f.write(f'lean_source "{puzzle.lean_source}\n"')
            f.write(f'lean_code {puzzle.lean_code}')
        # metadata section
        if puzzle.metadata:
            f.write('METADATA\n')
            for key, value in puzzle.metadata.items():
                f.write(f'{key} "{value}"\n')
        # definition section
        f.write('DEFINITION\n')
        if puzzle.cell_count_defined_in_file:
            f.write(f'cell_count {puzzle.cell_count}\n')
        if puzzle.cell_layout_defined_in_file:
            f.write(f'cell_layout {puzzle.cell_layout}\n')
        if puzzle.symbols_defined_in_file:
            f.write(f'symbols "{puzzle.symbols}"\n')
        if puzzle.import_constraints:
            f.write(f'imported_constraints\n')
            write_constraints(f,{key: value[0] for key, value in puzzle.import_constraints.items()})
        if puzzle.puzzle_level_constraints:
            f.write(f'constraints\n')
            write_constraints(f,puzzle.puzzle_level_constraints)
        if proof:
            f.write('PROOF\n')
            for line in proof:
                f.write(f'{line}\n')


if __name__ == '__main__':
    puzzle, proof = import_file('Puzzles/Framework/9x9Easy.suko')
    proof = [x[0] for x in proof] # get rid of line number information
    export_file('test.suko',puzzle,proof=proof)
