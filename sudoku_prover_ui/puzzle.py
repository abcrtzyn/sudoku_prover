

from dataclasses import dataclass
from io import TextIOWrapper
import sys
from typing import Dict, List, Tuple

from lark import Lark
from lark.visitors import Interpreter

class SukoInterpreter(Interpreter):
    _cell_count: int | None
    _cell_layout: List[Tuple[int,int]] | None
    _symbols: str | None
    _constraints: Dict[str,str]
    
    def __init__(self,is_puzzle:bool=True):
        self.is_puzzle = is_puzzle
        self._cell_count = None
        self._cell_layout = None
        self._symbols = None
        self._constraints = {}

    def suko(self, tree): # type: ignore
        # go parse the tree
        self.visit_children(tree) # type: ignore

        if self._cell_count is None:
            raise ValueError('No cell_count was given')
        if self._cell_layout is None:
            raise ValueError('No cell_layout was given')
        if len(self._cell_layout) != self._cell_count:
            raise ValueError('Number of cells in cell_layout did not match cell_count')
        if self._symbols is None:
            raise ValueError('No symbols object was provided')
        # TODO check that symbols can be found in lean
        # any other data validation we need

        return Puzzle(self._cell_count,self._cell_layout,self._symbols,self._constraints)

    def template_section(self, tree): #type: ignore





    # def cell_count(self,tree):




@dataclass
class Puzzle:
    cell_count: int
    cell_layout: List[Tuple[int,int]]
    symbols: str
    constraints: Dict[str,str]

    @staticmethod
    def import_puzzle(text: str):
        """text is from beginning of file to proof"""
        parser = Lark.open('suko.lark', parser='lalr',start='suko') #type:ignore
        tree = parser.parse(text) #type:ignore

        interpreter = SukoInterpreter()
        puzzle = interpreter.visit(tree) #type:ignore
        return puzzle

        
        

    def generate_lean_structure(self) -> str:
        raise NotImplementedError()


def main(argv: List[str]):
    """attempts to import the puzzle file provided by command line args
    used for testing purposes"""
    if len(argv) > 1:
        file = argv[1]
    else:
        print('provide a file to parse as an argument')
        exit()
    
    with open(file,'r') as f:
        text = f.read()

    parts = text.split("PROOF", 1)
    definition_text = parts[0]
    proof_text = parts[1] if len(parts) > 1 else ""

    puzzle = Puzzle.import_puzzle(definition_text)
    print(puzzle)





if __name__ == '__main__':
    main(sys.argv)
