

from dataclasses import dataclass, field
import re
from typing import Any, Dict, Generator, List, Tuple

# these tell python exactly what and in what order the symbols are
# very important
SYMBOLS_DICT: Dict[str,List[Any]] = {
    'Symbols4': [1,2,3,4],
    'SymbolsABCD': ['A','B','C','D'],
    'Symbols9': [1,2,3,4,5,6,7,8,9]
}


@dataclass
class Puzzle:
    metadata: Dict[str,str]
    cell_count: int
    cell_layout: List[Tuple[int,int]]
    symbols: str
    symbols_python: List[Any] = field(init=False)
    puzzle_level_constraints: Dict[str,str]
    # import constraints are keyed by the name, value[0] is the suko file name it imports from, value[1] is the lean code
    import_constraints: Dict[str,Tuple[str,str]]
    imported_constraints: Dict[str,str]
    pythonized_constraints: Dict[str,Tuple[str,Any]] = field(init=False)
    lean_imports: List[str]

    def __post_init__(self):
        # This runs immediately after __init__

        # go find the symbols definition
        if self.symbols not in SYMBOLS_DICT:
            raise ValueError(f'No python implementation of {self.symbols}')
        self.symbols_python = SYMBOLS_DICT[self.symbols]

        self.pythonized_constraints = {}
        # find python definitions for the constraints

        for c,code in self.qualified_constraints():
            if mat := re.match(r'f\s+(\d+)\s*=\s*(\w+)',code):
                # given digit constraint
                symbol = mat.group(2)
                if symbol.isnumeric():
                    symbol = int(symbol)
                if symbol not in self.symbols_python:
                    raise ValueError(f'Could not unify {symbol} with anything in {self.symbols_python}')
                self.pythonized_constraints[c] = ('Given',(int(mat.group(1)),symbol))
            elif mat := re.match(r'UniqueSet\s+f\s+({\s*\d+\s*(,\s*\d+\s*)*})',code):
                # UniqueSet
                cells = list(map(int, [item.strip() for item in mat.group(1).strip('{ }').split(',')]))
                self.pythonized_constraints[c] = ('UniqueSet',cells)
            else:
                # unknown constraint type
                raise ValueError(f'No python implementation of the lean code "{code}", it could also not have parsed correctly')


    def generate_lean_structure(self) -> str:
        definition = f"structure Puzzle (f: Nat -> {self.symbols}) where\n"
        definition += f"  outside_grid: ∀ x, x ≥ {self.cell_count} -> f x = {self.symbols_python[0]}\n"
        
        for name, constraint in self.top_level_constraints():
            definition += f"  {name}: {constraint}\n"
            

        return definition
    
    def top_level_constraints(self) -> Generator[Tuple[str,str],None,None]:
        yield from ((name, lean_code) for name, (_, lean_code) in self.import_constraints.items())
        yield from self.puzzle_level_constraints.items()
    
    def qualified_constraints(self) -> Generator[Tuple[str,str],None,None]:
        for constraint_dict in [self.imported_constraints, self.puzzle_level_constraints]:
            yield from constraint_dict.items()
                



@dataclass
class Template:
    # lean source file will be added to imports
    metadata: Dict[str,str] = field(init=False)
    lean_code: str
    cell_count: int | None
    cell_layout: List[Tuple[int,int]] | None
    symbols: str | None
    puzzle_level_constraints: Dict[str,str]
    import_constraints: Dict[str,Tuple[str,str]]
    imported_constraints: Dict[str,str]
    lean_imports: List[str]

    def top_level_constraints(self) -> Generator[Tuple[str,str],None,None]:
        yield from ((name, lean_code) for name, (_, lean_code) in self.import_constraints.items())
        yield from self.puzzle_level_constraints.items()
    
    def qualified_constraints(self) -> Generator[Tuple[str,str],None,None]:
        for constraint_dict in [self.imported_constraints, self.puzzle_level_constraints]:
            yield from constraint_dict.items()
