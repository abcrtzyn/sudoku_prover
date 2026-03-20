
import codecs
from dataclasses import dataclass, field
import re
import sys
from typing import Any, Dict, List, Tuple, cast

from lark import Lark, Token, Tree
from lark.visitors import Interpreter

# these tell python exactly what and in what order the symbols are
# very important
SYMBOLS_DICT: Dict[str,List[int]] = {
    'Symbols4': [1,2,3,4],
    'Symbols9': [1,2,3,4,5,6,7,8,9]
}


class SukoInterpreter(Interpreter): # pyright: ignore[reportMissingTypeArgument]
    _cell_count: int | None
    _cell_layout: List[Tuple[int,int]] | None
    _symbols: str | None
    _constraints: Dict[str,str]

    def __init__(self,file_name:str,is_puzzle:bool=True):
        self.is_puzzle = is_puzzle
        self.file_name = file_name
        self._cell_count = None
        self._cell_layout = None
        self._symbols = None
        self._constraints = {}

    def _clean_str(self, token: Token):
        # get rid of quotes
        raw: str = token.value[1:-1]
        # Unescape the backslashes
        return codecs.decode(raw, "unicode_escape")

    def suko(self, tree: Tree[Any]):
        # go parse the tree
        self.visit_children(tree) # pyright: ignore[reportUnknownMemberType]

        if self._cell_count is None:
            raise ValueError('No cell_count was given')
        if self._cell_layout is None:
            raise ValueError('No cell_layout was given')
        if len(self._cell_layout) != self._cell_count:
            raise ValueError('Number of cells in cell_layout did not match cell_count')
        if self._symbols is None:
            raise ValueError('No symbols object was provided')
        # TODO check that symbols can be found in lean

        rows, cols = zip(*self._cell_layout)
        min_row = min(rows)
        min_col = min(cols)

        # if the mins are not zero, offset the entire cell layout to make it 0.
        if min_row != 0 or min_col != 0:
            print('WARNING, the puzzle should have a cell in row 0 and column 0')
            print('it does not have to have a cell at (0,0) though')
            self._cell_layout = [(row-min_row,col-min_col) for row, col in self._cell_layout]
        
        # any other data validation we need

        return Puzzle(self._cell_count,self._cell_layout,self._symbols,self._constraints)

    def template_section(self, tree: Tree[Any]):
        if self.is_puzzle:
            raise Exception(f"{self.file_name}:{tree.meta.line}:{tree.meta.column} Can not create a puzzle from a suko TEMPLATE")
        raise NotImplementedError('template section is not implemented for a template')

    def parent_template(self, tree: Tree[Any]):
        file_path = self._clean_str(tree.children[0]) # pyright: ignore[reportArgumentType]
        print('parent_template is not implemented')



    def cell_count(self, tree: Tree[Any]):
        val = int(tree.children[0]) # pyright: ignore[reportArgumentType]
        if self._cell_count is not None and self._cell_count != val:
            # TODO show where the cell count was set previously
            raise ValueError(f"{self.file_name}:{tree.meta.line}:{tree.meta.column} Cell count was already set to {self._cell_count}")
        # either cell_count is none or the value is the same
        self._cell_count = val

    def cell_layout(self, tree: Tree[Any]):
        layout = cast(List[Tuple[int, int]],self.visit_children(tree)[0]) # pyright: ignore[reportUnknownMemberType]
        if self._cell_layout is not None and self._cell_layout != layout:
            # TODO show where the cell layout was set previously
            # TODO this will be a long error message, maybe just show where the last set was?
            raise ValueError(f"{self.file_name}:{tree.meta.line}:{tree.meta.column} Cell layout was already set to {self._cell_layout}")
        self._cell_layout = layout

    def _tuple(self, tree: Tree[Any]):
        return (int(tree.children[0]),int(tree.children[1])) # pyright: ignore[reportArgumentType]

    def symbols(self, tree: Tree[Any]):
        symbols = self._clean_str(tree.children[0]) # pyright: ignore[reportArgumentType]
        if self._symbols is not None and self._symbols != symbols:
            # TODO show where the symbols was set previously
            raise ValueError(f"{self.file_name}:{tree.meta.line}:{tree.meta.column} Symbols was already set to {self._symbols}")
        # TODO check that we can find the symbols lean object, maybe need to provide a symbols source field too, maybe this is the source.
        # the wierd thing about symbols compared to constraints is that the exact lean code is given to python for constraints in these files, but the definition of symbols is not...
        self._symbols = symbols

    def imported_constraint(self, tree: Tree[Any]):
        ident = tree.children[0].value # pyright: ignore[reportAttributeAccessIssue, reportUnknownMemberType]
        file_path = self._clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]
        print('imported_constraint not implemented')

    def imported(self, tree: Tree[Any]): # pyright: ignore[reportUnknownParameterType]
        # not sure what this will do yet, if anything
        return self.visit_children(tree) # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType]

    def constraint(self, tree: Tree[Any]):
        ident = cast(str,tree.children[0].value) # pyright: ignore[reportUnknownMemberType, reportAttributeAccessIssue]
        lean_code = self._clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]

        if ident in self._constraints:
            # TODO, locaation where the previous was defined
            raise Exception(f'{self.file_name}:{tree.meta.line}:{tree.meta.column} constraint {ident} already defined with definition "{self._constraints[ident]}"')
        self._constraints[ident] = lean_code

    # any rules that don't have a function to call end up here
    # if it is not in the doesn't have rule list, error out
    # otherwise, carry on with default behaviour
    def __default__(self, tree: Tree[Any]) -> Any:
        rule = tree.data
        if rule not in ['metadata_section','metadata_entry','definition_section','_list','local']:
            raise NotImplementedError(f"section '{tree.data}' not implemented yet\n")
        return self.visit_children(tree) # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType]

# steps and code stuffs for template importing
# def parent_template(self, tree):
#     path = tree.children[0].strip('"')
#     # RECURSION: Load the template file using the SAME logic
#     parent = Puzzle.load_puzzle(path, is_puzzle=False)
#     self.puzzle.merge(parent)

    # path = tree.children[0].strip('"')
    # # Load the parent file
    # parent_puzzle = Puzzle.load_puzzle(path, is_puzzle=False)
    # # Merge parent data into OUR temporary state
    # if parent_puzzle.cell_count:
    #     if self._cell_count and self._cell_count != parent_puzzle.cell_count:
    #         raise ValueError("Template count conflicts with local count")
    #     self._cell_count = parent_puzzle.cell_count
    # # ... repeat for layout, symbols, etc.

# in the class
# self.seen_files = seen_files or set()
    # # 1. Resolve to an absolute path
    # relative_path = tree.children.strip('"')
    # abs_path = os.path.abspath(relative_path)
    # # 2. Check for circular reference
    # if abs_path in self.seen_files:
    #     raise RecursionError(f"Circular template reference detected: {abs_path}")
    # # 3. Add to stack and recurse
    # new_seen = self.seen_files.copy()
    # new_seen.add(abs_path)
    # # Pass the 'seen' set to the next interpreter
    # parent_puzzle = Puzzle.load_puzzle(abs_path, is_puzzle=False, seen_files=new_seen)
    # # 4. Merge logic...
    # self.puzzle.merge(parent_puzzle)


@dataclass
class Puzzle:
    cell_count: int
    cell_layout: List[Tuple[int,int]]
    symbols: str
    symbols_python: List[int] = field(init=False)
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
            if mat := re.match(r'f\s+(\d+)\s*=\s*(\d+)',code):
                # given digit constraint
                self.constraints_python[c] = ('Given',(int(mat.group(1)),int(mat.group(2))))
            elif mat := re.match(r'UniqueSet\s+f\s+({\s*\d+\s*(,\s*\d+\s*)*})',code):
                # UniqueSet
                cells = list(map(int, [item.strip() for item in mat.group(1).strip('{ }').split(',')]))
                self.constraints_python[c] = ('UniqueSet',cells)
            else:
                # unknown constraint type
                raise ValueError(f'No python implementation of the lean code "{code}", it could also not have parsed correctly')




    @staticmethod
    def import_puzzle(text: str,file_name:str):
        """text is from beginning of file to proof"""
        parser = Lark.open('suko.lark', parser='lalr',start='suko',propagate_positions=True) # pyright: ignore[reportUnknownMemberType]
        tree = parser.parse(text) # pyright: ignore[reportUnknownMemberType]

        interpreter = SukoInterpreter(file_name)
        puzzle = cast(Puzzle,interpreter.visit(tree)) # pyright: ignore[reportUnknownMemberType]
        return puzzle




    def generate_lean_structure(self) -> str:
        definition = f"puzzle = structure Puzzle (f: Nat -> {self.symbols}) where\n"
        definition += f"  outside_grid: ∀ x, x ≥ 16 -> solution x = {self.symbols_python[0]}\n"
        for name, constraint in self.constraints.items():
            if '.' in name:
                raise NotImplementedError('we are not able to handle template constraints yet')
            definition += f"  {name}: {constraint}\n"


        return definition


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

    puzzle = Puzzle.import_puzzle(definition_text,file)
    print(puzzle)





if __name__ == '__main__':
    main(sys.argv)
