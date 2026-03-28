
import codecs
import os
from typing import Any, Dict, List, Set, Tuple, cast

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
    _name: str | None
    def _add_name(self,name: str):
        if self._name is not None and self._name != name:
            raise ValueError('duplicate name given')
        self._name = name

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
    
    _qualified_constraints: Dict[str,str]
    _constraints: Dict[str,str]
    def _add_constraint(self,name:str,constraint:str):
        # this is for all top level contsraints, adds them to both sets
        if name.find('.') > 0:
            raise Exception(f'dot notation in constraint names is reserved for imported constraints, {name} is invalid')
        if name in self._qualified_constraints:
            raise Exception(f'constraint {name} already defined with definition "{self._constraints[name]}"')
        self._qualified_constraints[name] = constraint
        self._constraints[name] = constraint
        

    def _add_imported_contstraint(self,ident:str,lean_name:str,constraints:Dict[str,str]):
        # this is for all imported constraints
        if ident.find('.') > 0:
            raise Exception(f'dot notation in constraint names is reserved for imported constraints, {ident} is invalid')
        if ident in self._constraints:
            raise Exception(f'constraint {ident} already defined with definition "{self._constraints[ident]}"')
        self._constraints[ident] = f'{lean_name} f'
        for name, constraint in constraints.items():
            name = f'{ident}.{name}'
            if name in self._qualified_constraints:
                raise Exception(f'constraint {name} already defined with definition "{self._qualified_constraints[name]}"')
            self._qualified_constraints[name] = constraint


    _lean_imports: List[str] # a list of lean modules (files) to import
    def _add_lean_imports(self,lean_imports:List[str]):
        for imp in lean_imports:
            if imp not in self._lean_imports:
                self._lean_imports.append(imp)
    

    def __init__(self,file_name:str,seen_files:Set[str],is_puzzle:bool=True):
        self.is_puzzle = is_puzzle
        self.file_name = file_name
        self._metadata: Dict[str,str] = {}
        self._name = None
        self._cell_count = None
        self._cell_layout = None
        self._symbols = None
        self._qualified_constraints = {}
        self._constraints = {}
        self._lean_imports = []
        self.seen_files = seen_files
    
    def puzzle_definition(self, tree: Tree[Any]):
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

            return Puzzle(self._metadata,self._cell_count,self._cell_layout,self._symbols,self._qualified_constraints,self._constraints,self._lean_imports)

        else:
            # its a template
            # no data validation here
            if self._name is None:
                raise ValueError(f'{self.file_name} Template files are required to have the name field in the metadata, this is how to address it')
            return Template(self._metadata,self._name,self._cell_count,self._cell_layout,self._symbols,self._qualified_constraints,self._constraints,self._lean_imports)


    def template_section(self, tree: Tree[Any]):
        if self.is_puzzle:
            raise Exception(f"{self.file_name}:{tree.meta.line}:{tree.meta.column} Can not create a puzzle from a suko TEMPLATE")
        lean_module = clean_str(self.visit_children(tree)[0]) # pyright: ignore[reportUnknownArgumentType, reportUnknownMemberType]
        self._add_lean_imports([lean_module])
    
    def metadata_entry(self, tree: Tree[Any]):
        key = tree.children[0].value # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType, reportAttributeAccessIssue]
        value = clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]
        if key == 'name':
            self._add_name(value) # pyright: ignore[reportArgumentType]
        self._metadata[key] = value
            
    def _import_template(self,file_name:str,ident:str,tree: Tree[Any]):
        puzzle, _ = cast(Tuple[Template,Any],import_file(file_name,is_puzzle=False,seen_files=self.seen_files))
        
        if puzzle.cell_count is not None:
            self._add_cell_count(puzzle.cell_count) 
        if puzzle.cell_layout is not None:
            self._add_cell_layout(puzzle.cell_layout)
        if puzzle.symbols is not None:
            self._add_symbols(puzzle.symbols)
        # for constraints, we can ignore the normal constraints and just do the qualified ones
        # this is because the template that we are currently parsing will be the object that goes in constraints
        self._add_imported_contstraint(ident,puzzle.name,puzzle.qualified_constraints)
        self._add_lean_imports(puzzle.lean_imports)


    def parent_template(self, tree: Tree[Any]):
        file_path = clean_str(tree.children[0]) # pyright: ignore[reportArgumentType]
        self._import_template(file_path,'base',tree)



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
        # i believe that this code is exact same as a template, just with a name
        # maybe constraints aren't supposed to have a cell layout...
        ident = cast(str,tree.children[0].value)  # pyright: ignore[reportUnknownMemberType, reportAttributeAccessIssue]
        file_path = clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]
        self._import_template(file_path,ident,tree)

    def imported(self, tree: Tree[Any]): # pyright: ignore[reportUnknownParameterType]
        # not sure what this will do yet, if anything
        return self.visit_children(tree) # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType]

    def constraint(self, tree: Tree[Any]):
        ident = cast(str,tree.children[0].value) # pyright: ignore[reportUnknownMemberType, reportAttributeAccessIssue]
        lean_code = clean_str(tree.children[1]) # pyright: ignore[reportArgumentType]
        self._add_constraint(ident,lean_code)


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
            raise ValueError(f'{file_name} PROOF section is not allowed in a file that is not meant to be a puzzle')
        interpreter = ProofInterpreter(file_name)
        proof_text = cast(List[Tuple[str,int]],interpreter.visit(tree.children[1])) # pyright: ignore[reportUnknownMemberType, reportArgumentType]
    else:
        proof_text = []

    # we are done with this file, get rid of it
    seen_files.remove(file_name)
    return (puzzle,proof_text)
