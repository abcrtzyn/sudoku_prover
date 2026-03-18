

import ast
from dataclasses import dataclass
from io import TextIOWrapper
from typing import Dict, List, Tuple

def expect(s: str,line: str):
    """expects a string s, if it doesn't get it, error out"""
    if s != line:
        raise ValueError(f"expected {s} but got {line}")

def parse_cell_layout(line: str) -> List[Tuple[int,int]]:
    # if we switch to a multiline format, we need to inculed the file pointer
    raise NotImplementedError('parse_cell_layout is not implemented yet.')

def parse_imported_constraints(fp) -> Dict[str,str]:
    # basically this is reading another template file, but the file should not have any other field than imported constraints or constraints
    raise NotImplementedError('parse_imported_constraints is not implemented yet.')




@dataclass
class Template:
    """Template represents a potential puzzle, one that is merely unfinished
    It may even include it's own templates..."""
    cell_count: int | None
    cell_layout: List[Tuple[int,int]] | None
    symbols: str | None
    constraints: Dict[str,str]

    @staticmethod
    def import_from_file(fp: TextIOWrapper) -> Template:
        """Reads everything from DEFINITION to an unknown thing or EOF"""
        expect("DEFINITION",fp.readline().strip().upper())
        template: Template | None = None
        cell_count: int | None= None
        cell_layout: List[Tuple[int,int]] | None = None
        symbols: str | None = None
        constraints: Dict[str,str] = {}

        while True:
            line = fp.readline().rstrip()
            # should be looking at key value pairs now (mostly)
            line_items = line.split()
            key = line_items[0]
            match key:
                case "template":
                    file_path = line.removeprefix('template').strip()
                    template = Template.import_from_file(file_path)
                case "cell_count":
                    cell_count = int(line.removeprefix('cell_count').strip())
                    if cell_count < 0:
                        raise ValueError(f"cell_count must be positive, I think organisms need at least one cell to do anything? line is {line}")
                case "cell_layout":
                    cell_layout = parse_cell_layout(line.removeprefix('cell_layout').strip())
                case "symbols":
                    symbols = ast.literal_eval(line.removeprefix('symbols').strip())
                case "imported_constraints":
                    imp_cons = parse_imported_constraints(fp)
                    for c in imp_cons:
                        if c in constraints:
                            ValueError(f'duplicate constraint name {c} imported as {imp_cons[c]} and existing as {constraints[c]}')
                        constraints[c] = imp_cons[c]
                case ""




                case _:
                    raise ValueError(f"don't know what to do with a the key {key} in line {line}")



    @staticmethod
    def import_from_file_path(file_path: str) -> Template:
        """This reads an entire template file"""
        with open(file_path) as fp:
            expect("TEMPLATE",fp.readline().strip().upper())
            temp = Template.import_from_file(fp)
            # TODO check that proof does not appear
        return temp
        


@dataclass
class Puzzle:
    cell_count: int
    cell_layout: List[Tuple[int,int]]
    symbols: str
    constraints: Dict[str,str]

    
    @staticmethod
    def import_from_file(fp: TextIOWrapper) -> Puzzle:
        """This reads everything starting from DEFINITION to PROOF"""
        puzzle_temp = Template.import_from_file(fp)
        # check that puzzle temp has all the required fields.
        # then return
        this = Puzzle()

    def generate_lean_structure(self) -> str:
        raise NotImplementedError()


