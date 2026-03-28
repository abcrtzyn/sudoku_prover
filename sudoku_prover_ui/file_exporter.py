"""Take an object from Puzzle class and export it to a suko file"""

import hashlib
from pathlib import Path
from typing import List
from sudoku_prover_ui.file_parser import import_file
from sudoku_prover_ui.puzzle import Puzzle, Template

grammar_file = Path(__file__).resolve().parent.parent.joinpath('suko.lark')

EXPECTED_HASH = "75cb68f4" # current version

with open(grammar_file, 'rb') as f:
    current = hashlib.md5(f.read()).hexdigest()[:8]
    if current != EXPECTED_HASH:
        print('warning: grammar has been changed, export file may not result in the same format. new hash value {current}')


def export_file(filename: str, puzzle: Puzzle | Template, is_puzzle: bool = True, *, proof: List[str] = []):
    if not is_puzzle and proof:
        raise ValueError('template can not have a proof')
    with open(filename, 'w+') as f:
        if not is_puzzle:
            # template section
            f.write('TEMPLATE\n')
            f.write(f'lean_source "{'todo'}\n"')
        # metadata section
        f.write('METADATA\n')
        for key, value in puzzle.metadata.items():
            f.write(f'{key} "{value}"\n')
        # definition section
        f.write('DEFINITION\n')
        f.write(f'cell_count {puzzle.cell_count}\n')
        f.write(f'cell_layout {puzzle.cell_layout}\n')
        f.write(f'symbols "{puzzle.symbols}"\n')
        f.write(f'imported_constraints\n')
        print(puzzle.constraints)
        print(puzzle.qualified_constraints)
        exit()

if __name__ == '__main__':
    puzzle, proof = import_file('Puzzles/Framework/9x9Easy.suko')
    export_file('test.suko',puzzle,proof=True)
