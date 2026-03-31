
import codecs
import os
from typing import Any, Dict, List, Literal, Set, Tuple, cast, overload

from lark import Lark, Token, Tree
from lark.exceptions import UnexpectedInput
from lark.visitors import Interpreter

from sudoku_prover_ui.puzzle import Puzzle, Template

class FileParseError(Exception):
    pass

def clean_str(token: Token):
        # get rid of quotes
        raw: str = token.value[1:-1]
        # Unescape the backslashes
        return codecs.decode(raw, "unicode_escape")



class PuzzleInterpreter(Interpreter): # pyright: ignore[reportMissingTypeArgument]
    
    _cell_count: int | None
    def _add_cell_count(self,cell_count: int):
        if self._cell_count is not None and self._cell_count != cell_count:
            raise ValueError('duplicate cell_count given')
        self._cell_count = cell_count
    
    _cell_layout: List[Tuple[int,int]] | None
    def _add_cell_layout(self,cell_layout: List[Tuple[int,int]]):
        if self._cell_layout is not None and self._cell_layout != cell_layout:
            raise ValueError('duplicate cell_layout given')
        self._cell_layout = cell_layout

    _symbols: str | None
    def _add_symbols(self,symbols: str):
        if self._symbols is not None and self._symbols != symbols:
            raise ValueError('duplicate symbols given')
        self._symbols = symbols
    
    _puzzle_level_constraints: Dict[str,str]
    _import_constraints: Dict[str,Tuple[str,str]]
    _imported_constraints: Dict[str,str]

    _lean_imports: List[str] # a list of lean modules (files) to import
    def _add_lean_imports(self,lean_imports:List[str]):
        for imp in lean_imports:
            if imp not in self._lean_imports:
                self._lean_imports.append(imp)
    

    def __init__(self,file_name:str,seen_files:Set[str],is_puzzle:bool=True):
        self.is_puzzle = is_puzzle
        self.file_name = file_name
        self._metadata: Dict[str,str] = {}
        self._lean_source: str | None = None
        self._lean_code: str | None = None
        self._cell_count: int | None = None
        self._cell_layout: List[Tuple[int,int]] | None = None
        self._symbols: str | None = None
        self._puzzle_level_constraints: Dict[str,str] = {}
        self._import_constraints = {}
        self._imported_constraints: Dict[str,str] = {}
        self._lean_imports = []
        self.seen_files = seen_files
    
    def puzzle_definition(self, tree: Tree[Any]):
        if tree.children[0].data == 'template_section' and self.is_puzzle:
            raise ValueError('This file is a template, I the parser was expecting a puzzle')
        if tree.children[0].data != 'template_section' and not self.is_puzzle:
            raise ValueError('This file is a puzzle, I the parser was expecting a template')
        
        self.visit_children(tree) # pyright: ignore[reportUnknownMemberType]

        if self.is_puzzle:
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

            return Puzzle(
                self._metadata,
                self._cell_count,
                self._cell_layout,
                self._symbols,
                self._puzzle_level_constraints,
                self._import_constraints,
                self._imported_constraints,
                self._lean_imports)

        else:
            # its a template
            if self._lean_code is None:
                raise ValueError('No lean_code was given in the template section')


            return Template(
                self._lean_source,
                self._lean_code,
                self._cell_count,
                self._cell_layout,
                self._symbols,
                self._puzzle_level_constraints,
                self._import_constraints,
                self._imported_constraints,
                self._lean_imports)


    def template_section(self, tree: Tree[Any]):
        if self.is_puzzle:
            raise Exception(f"{self.file_name}:{tree.meta.line}:{tree.meta.column} Can not create a puzzle from a suko TEMPLATE")
        lean_module = clean_str(tree.children[0]) # pyright: ignore[reportArgumentType]
        lean_code = clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]
        self._lean_source = lean_module
        self._add_lean_imports([lean_module])
        self._lean_code = lean_code
    
    def metadata_entry(self, tree: Tree[Any]):
        key = tree.children[0].value # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType, reportAttributeAccessIssue]
        value = clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]
        self._metadata[key] = value
            
    def _import_template(self,file_name:str,ident:str,tree: Tree[Any]):
        puzzle, _ = import_file(file_name,is_puzzle=False,seen_files=self.seen_files)
        
        if puzzle.cell_count is not None:
            self._add_cell_count(puzzle.cell_count) 
        if puzzle.cell_layout is not None:
            self._add_cell_layout(puzzle.cell_layout)
        if puzzle.symbols is not None:
            self._add_symbols(puzzle.symbols)
        
        self._add_lean_imports(puzzle.lean_imports)

        self._import_constraints[ident] = (file_name,puzzle.lean_code)
        # all puzzle_level and imported need to be added to imported, don't care about import
        for name, constraint in puzzle.qualified_constraints():
            new_name = f'{ident}.{name}'
            # this is for top level constraints
            if new_name in self._puzzle_level_constraints:
                raise ValueError(f'constraint {new_name} already defined with definition "{self._puzzle_level_constraints[new_name]}"')
            elif new_name in self._imported_constraints:
                raise ValueError(f'constraint {new_name} already defined with definition "{self._imported_constraints[new_name]}"')

            self._imported_constraints[new_name] = constraint

    def cell_count(self, tree: Tree[Any]):
        val = int(tree.children[0]) # pyright: ignore[reportArgumentType]
        self._add_cell_count(val)

    def cell_layout(self, tree: Tree[Any]):
        layout = cast(List[Tuple[int, int]],self.visit_children(tree)[0]) # pyright: ignore[reportUnknownMemberType]
        self._add_cell_layout(layout)

    def _tuple(self, tree: Tree[Any]):
        return (int(tree.children[0]),int(tree.children[1])) # pyright: ignore[reportArgumentType]

    def symbols(self, tree: Tree[Any]):
        symbols = clean_str(tree.children[0]) # pyright: ignore[reportArgumentType]
        self._add_symbols(symbols)

    def imported_constraint(self, tree: Tree[Any]):
        ident = cast(str,tree.children[0].value)  # pyright: ignore[reportUnknownMemberType, reportAttributeAccessIssue]
        file_path = clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]
        self._import_template(file_path,ident,tree)

    def imported(self, tree: Tree[Any]): # pyright: ignore[reportUnknownParameterType]
        # not sure what this will do yet, if anything
        return self.visit_children(tree) # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType]

    def constraint(self, tree: Tree[Any]):
        ident = cast(str,tree.children[0].value) # pyright: ignore[reportUnknownMemberType, reportAttributeAccessIssue]
        lean_code = clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]
        # this is for top level constraints
        if ident in self._puzzle_level_constraints:
            raise ValueError(f'constraint {ident} already defined with definition "{self._puzzle_level_constraints[ident]}"')
        elif ident in self._imported_constraints:
            raise ValueError(f'constraint {ident} already defined with definition "{self._imported_constraints[ident]}"')

        self._puzzle_level_constraints[ident] = lean_code


    # any rules that don't have a function to call end up here
    # if it is not in the doesn't have rule list, error out
    # otherwise, carry on with default behaviour
    def __default__(self, tree: Tree[Any]) -> Any:
        rule = tree.data
        if rule not in ['metadata_section','definition_section','_list','local']:
            raise NotImplementedError(f"section '{tree.data}' not implemented yet\n")
        return self.visit_children(tree) # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType]


class ProofInterpreter(Interpreter): # pyright: ignore[reportMissingTypeArgument]
    def __init__(self,file_name:str):
        self.file_name = file_name
    
    def proof_line(self, tree: Tree[Any]) -> Tuple[str,int]:
        return (tree.children[0].value,tree.meta.line) # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType, reportAttributeAccessIssue, reportArgumentType]

    # any rules that don't have a function to call end up here
    # if it is not in the doesn't have rule list, error out
    # otherwise, carry on with default behaviour
    def __default__(self, tree: Tree[Any]) -> Any:
        rule = tree.data
        if rule not in ['proof_section']:
            raise NotImplementedError(f"section '{tree.data}' not implemented yet\n")
        return self.visit_children(tree) # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType]



@overload
def import_file(file_name: str, is_puzzle: Literal[True] = True, seen_files: Set[str] | None = None) -> Tuple[Puzzle, List[Tuple[str, int]]]: ...
@overload
def import_file(file_name: str, is_puzzle: Literal[False], seen_files: Set[str] | None = None) -> Tuple[Template, List[Tuple[str,int]]]: ...

def import_file(file_name: str,is_puzzle: bool = True, seen_files: Set[str] | None = None):
    # change the file to a full path for error reporting
    if file_name:
        file_name = os.path.abspath(file_name)
    
    if seen_files is not None:
        if file_name in seen_files:
            raise RecursionError(f"Circular import detected, {file_name} has already been imported")
        seen_files.add(file_name)
    else:
        # if it is none, start it up
        seen_files = {file_name}

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
    
    parser = Lark.open('suko.lark', parser='lalr',start='suko',propagate_positions=True) # pyright: ignore[reportUnknownMemberType]
    try:
        tree = parser.parse(text) # pyright: ignore[reportUnknownMemberType]
    except UnexpectedInput as e:
        e.add_note(f"{file_name}:{e.line}:{e.column}")
        raise e

    interpreter = PuzzleInterpreter(file_name, seen_files, is_puzzle)
    puzzle = cast(Puzzle | Template,interpreter.visit(tree.children[0])) # pyright: ignore[reportArgumentType, reportUnknownMemberType]
    if len(tree.children) > 1:
        assert len(tree.children) == 2
        if not is_puzzle:
            raise ValueError(f'{file_name} PROOF section is not allowed in a template file')
        interpreter = ProofInterpreter(file_name)
        proof_text = cast(List[Tuple[str,int]],interpreter.visit(tree.children[1])) # pyright: ignore[reportUnknownMemberType, reportArgumentType]
    else:
        proof_text = []

    # we are done with this file, get rid of it
    seen_files.remove(file_name)
    return (puzzle,proof_text)


if __name__ == "__main__":
    puzzle, proof = import_file('Puzzles/Framework/9x9Easy.suko')
    print(puzzle)
    print(proof)
