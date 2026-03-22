

from dataclasses import dataclass, field
import re
import sys
from typing import Any, Dict, List, Tuple, cast

# these tell python exactly what and in what order the symbols are
# very important
SYMBOLS_DICT: Dict[str,List[Any]] = {
    'Symbols4': [1,2,3,4],
    'SymbolsABCD': ['A','B','C','D'],
    'Symbols9': [1,2,3,4,5,6,7,8,9]
}


@dataclass
class Puzzle:
    cell_count: int
    cell_layout: List[Tuple[int,int]]
    symbols: str
    symbols_python: List[Any] = field(init=False)
    constraints: Dict[str,str]
    constraints_python: Dict[str,Tuple[str,Any]] = field(init=False)

    def __post_init__(self):
        # This runs immediately after __init__

        # go find the symbols definition
        if self.symbols not in SYMBOLS_DICT:
            raise ValueError(f'No python implementation of {self.symbols}')
        self.symbols_python = SYMBOLS_DICT[self.symbols]

        self.constraints_python = {}
        # find python definitions for the constraints
        for c,code in self.constraints.items():
            if mat := re.match(r'f\s+(\d+)\s*=\s*(\w+)',code):
                # given digit constraint
                symbol = mat.group(2)
                if symbol.isnumeric():
                    symbol = int(symbol)
                if symbol not in self.symbols_python:
                    raise ValueError(f'Could not unify {symbol} with anything in {self.symbols_python}')
                self.constraints_python[c] = ('Given',(int(mat.group(1)),symbol))
            elif mat := re.match(r'UniqueSet\s+f\s+({\s*\d+\s*(,\s*\d+\s*)*})',code):
                # UniqueSet
                cells = list(map(int, [item.strip() for item in mat.group(1).strip('{ }').split(',')]))
                self.constraints_python[c] = ('UniqueSet',cells)
            else:
                # unknown constraint type
                raise ValueError(f'No python implementation of the lean code "{code}", it could also not have parsed correctly')


    def generate_lean_structure(self) -> str:
        definition = f"puzzle = structure Puzzle (f: Nat -> {self.symbols}) where\n"
        definition += f"  outside_grid: ∀ x, x ≥ 16 -> f x = {self.symbols_python[0]}\n"
        for name, constraint in self.constraints.items():
            if '.' in name:
                raise NotImplementedError('we are not able to handle template constraints yet')
            definition += f"  {name}: {constraint}\n"


        return definition
