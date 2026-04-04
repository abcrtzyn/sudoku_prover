
from contextlib import contextmanager
import re
from typing import Any, Dict, Generator, List, Tuple

from sudoku_prover_ui.journal import Delta, Journal, State
from sudoku_prover_ui.lean_repl import LeanLspRepl
from sudoku_prover_ui.puzzle import Puzzle
from sudoku_prover_ui.sudoku_state import SudokuState

from pathlib import Path

# __file__ is .../sudoku_prover_ui/proof_engine.py
# .parent is .../sudoku_prover_ui/
# .parent.parent is the repo root
REPO_ROOT = Path(__file__).resolve().parent.parent



word_to_number = {
    'one': 1,
    'two': 2,
    'three': 3,
    'four': 4,
    'five': 5,
}


class CommandError(Exception):
    pass


class ProofEngine:
    current: State
    journal: Journal

    def __enter__(self):
        return self.setup()
    
    def close(self):
        self.repl.close()

    def __exit__(self, *args): # pyright: ignore[reportMissingParameterType, reportUnknownParameterType]
        self.close()


    def __init__(self, puzzle: Puzzle):
        self.repl = LeanLspRepl(REPO_ROOT) # pyright: ignore[reportArgumentType]
        self.puzzle = puzzle
        self._active_gen: Generator[str, str, None]
        self.terminal_prompt: str
        self._place_dot: bool = False
        self.prepared_text = ''

#     def setup(self):
#         self.repl.open()

#         self.current = State()


#         try:
#             # imports
#             import_text = ''
#             for imp in ['Mathlib.Tactic.IntervalCases','SudokuProverLogic.Basic',
#                         f'SudokuProverLogic.{self.puzzle.symbols}','SudokuProverLogic.Tactics'] + self.puzzle.lean_imports:
#                 import_text += f'import {imp}\n'
#             self.repl.run_command(import_text)

#             # set options, maybe we will format how lean wants later, but I don't care
#             self.repl.run_command('set_option linter.style.whitespace false\nset_option linter.style.longLine false\n')
            
#             # give the puzzle to Lean
#             self.repl.run_command(self.puzzle.generate_lean_structure())
            
#             # create the state
#             grid: List[int | None] = [None for _ in range(self.puzzle.cell_count)]
#             eliminations: Dict[int,Dict[int,Tuple[str,Any]]] = {}
#             self.current = SudokuState([],grid,eliminations)

#             # this keeps track of what level of proof we are on, it also determines how much indent there is
#             # indent is 2*proof_level
#             # any lemma or have block increases this by one, also any cases will but with the exception of the center dots
#             self.proof_level = 0

#             # start with any initial constraints, might just be given digits
#             # anything that I would consider part of the solution that is given gets processed here
#             for name, constraint in self.puzzle.pythonized_constraints.items():
#                 match constraint[0]:
#                     case 'Given':
#                         cell = constraint[1][0]
#                         digit = constraint[1][1]
#                         self.tactic(f"lemma c{cell} {{f: Nat -> {self.puzzle.symbols}}} (P: Puzzle f): f {cell} = {digit} := P.{name}")
                
#                         # create elimination proofs for each
#                         self.current.grid[cell] = digit
#                         self.region_eliminate(cell,digit,f'c{cell}')
#                     case 'UniqueSet':
#                         pass
#                     case _:
#                         raise NotImplementedError(f'constraint of type {constraint[0]} has no implementation for initialization')
            
#             # get a new line in there for spacing reasons
#             self.tactic('')
#             self._send_proof()
                    
#             self._active_gen = self.controller()
#             self.terminal_prompt = next(self._active_gen)
#         except:
#             self.close()
#             raise

#         return self

#     def place_dot(self):
#         self._place_dot = True

#     @contextmanager
#     def indent(self):
#         """Increments proof level, and decrements after."""
#         self.proof_level += 1
#         try:
#             yield
#         finally:
#             self.proof_level -= 1

#     def tactic(self, tactic: str):
#         """helper that handles the state variables
#         updates the proof state and returns it"""
#         tactic_text = ''
#         for line in tactic.splitlines(True):
#             tactic_text += f'{'  '*(self.proof_level-self._place_dot)}{'· ' if self._place_dot else ''}{line}'
#             self._place_dot = False

#         # print(tactic_text)
#         self.prepared_text += tactic_text + '\n'

#     def _send_proof(self):
#         goals, diags = self.repl.run_command(self.prepared_text)
#         self.prepared_text = ''
#         self.current.proof_state = goals
#         return self.current.proof_state, diags


#     def _execute_or_prompt(self, command: Generator[str, str, None] | None, prompt: str) -> Generator[str, str, None]:
#         """if a command is given, run the command, else, get one from the interface and run it"""
#         if command is not None:
#             yield from command
#         else:
#             cmd = yield prompt
#             yield from self.handle_input(cmd)
    
#     def _execute_dict_or_prompt[K](self, commands: Dict[K,Generator[str,str,None]] | None, key: K, prompt: str) -> Generator[str, str, None]:
#         """if a command is given, run the command, else, get one from the interface and run it"""
#         if commands is not None and key in commands:
#             yield from commands[key]
#         else:
#             cmd = yield prompt
#             yield from self.handle_input(cmd)

#     def region_eliminate(self, cell: int,digit: int,proof_name:str):
#         """eliminates all of digit from every cell in every region that cell is a part of"""
#         for name, constraint in self.puzzle.pythonized_constraints.items():
#             if constraint[0] != 'UniqueSet':
#                 continue
#             if cell in constraint[1]:
#                 for i in constraint[1]:
#                     if i == cell:
#                         continue        
#                     # we have a choice to override a current elimination rule, or keep the first one
#                     # there are pros and cons to either, but that is for future me to decide.
#                     # this code OVERRIDES existing elemination rules
#                     if i not in self.current.eliminations:
#                         self.current.eliminations[i] = dict()
#                     self.current.eliminations[i][digit] = ('digit_in_region', (cell,name,proof_name))


#     def generate_elimination_proof(self,cell: int, digit: int, hypothesis: str):
#         """Given the current cell and digit and hypothesis name to eliminate
#         eliminates this contradictory case"""
        
#         if self.current.grid[cell] is not None:
#             proof = f'exact digit_in_cell {hypothesis} (c{cell} P)'
#             self.tactic(f'exfalso; {proof}')
#         elif cell in self.current.eliminations and digit in self.current.eliminations[cell]:
#             elim = self.current.eliminations[cell][digit]
#             if elim[0] == 'digit_in_region':
#                 proof = f'exact digit_in_region {hypothesis} P.{elim[1][1]} ({elim[1][2]} P)'
#             else:
#                 print('unknown elimination reason',elim[0])
#                 exit(4)
#             self.tactic(f'exfalso; {proof}')
#         else:
#             print(f'no elimination present for {cell} {digit}')
#             exit(5)

#     def have(self, name: str, goal: str, command: Generator[str,str,None] | None = None) -> Generator[str,str,None]:
#         """generates a have goal in Lean, can be anything at this point, there will be rules later..."""

#         # if it is a top level goal, need to start a new lemma, otherwise do a have statement
#         if self.proof_level == 0:
#             self.tactic(f"lemma {name} {{f: Nat -> {self.puzzle.symbols}}} (P: Puzzle f): {goal} := by")
#         else:
#             self.tactic(f"have {name}: {goal} := by")
        

#         with self.indent():
#             # solve the goal using a command
#             yield from self._execute_or_prompt(command,goal)

#         # add a newline
#         self.tactic('')
        


#     def fill(self, cell: int, digit: int, command: Generator[str,str,None] | None = None) -> Generator[str,str,None]:
#         """special case to fill a cell with a digit, creates the goal and after is proved, adds it to the datastructures and creates eliminations"""
#         yield from self.have(f'c{cell}', f'f {cell} = {digit}',command)
        
#         self.current.grid[cell] = digit
#         self.region_eliminate(cell,digit,f'c{cell}')

#     def cell_cases(self, cell: int, commands: Dict[int,Generator[str,str,None]] | None = None) -> Generator[str,str,None]:
#         self.tactic(f'cases h: f {cell}')
        
#         with self.indent():
#             # we know the order of these cases, it's exactly the order of the symbols
#             for digit in self.puzzle.symbols_python:
#                 self.place_dot()
#                 if cell in self.current.eliminations and digit in self.current.eliminations[cell]:
#                     self.generate_elimination_proof(cell,digit,'h')
#                     # TODO we also need to check for accepting cases, not yet
#                 else:
#                     yield from self._execute_dict_or_prompt(commands,digit,f'cell_cases {digit}')
            
        

#     def support_cases(self, hypothesis: str, digit: int | None, commands: Dict[int,Generator[str,str,None]] | None = None) -> Generator[str,str,None]:
#         """Does support_cases or locked_support_cases on the hypothesis and digit
#         the hypothesis is must be of the form SupportSet {...} n or LockedSet {...} {...}
#         This function will detect which one is needed. If the hypothesis is a locked set, a digit must be given"""
#         for var in self.current.proof_state.goals[0].variables:
#             if var.name == hypothesis:
#                 break
#         else:
#             print(f'could not find a hypothesis {hypothesis} in the context')
#             exit(2)
#         pattern = r'(?P<type>Locked|Support)Set f \{(?P<data>\d+(?:,\s*\d+)*)\} (?P<digit>\S|.+)'
#         mat = re.match(pattern, var.t)
#         if mat is None:
#             print(f'{var.t} did not match the re')
#             exit(7)
#         region_is_locked = mat.group('type') == 'Locked'
#         cell_set = [int(x.strip()) for x in mat.group('data').split(',')]
#         # if it is a support set, get the digit from the hypothesis
#         if not region_is_locked:
#             digit = int(mat.group('digit'))
        
#         if digit is None:
#             print('no digit provided for locked set')
#             exit(8)
#         self.tactic(f"""{'locked_support_cases' if region_is_locked else 'support_cases'} h {digit}""")
#         with self.indent():
#             for cell in cell_set:
#                 self.place_dot()
#                 if (self.current.grid[cell] is not None) or (cell in self.current.eliminations and digit in self.current.eliminations[cell]):
#                     self.generate_elimination_proof(cell,digit,'h')
#                 # TODO we also need to check for accepting cases, not yet
#                 else:
#                     yield from self._execute_dict_or_prompt(commands,cell,f'support_cases {cell}')
            
        
#     def support_cases_manual(self, digit: int, region: str) -> Generator[str,str,None]:
#         # couple things we have to do in order to call support cases
#         # one, create the hypothesis to run cases on, which has many cases
#         # is there a hypothesis by that name in the context?
#         qualified_region_name = None
#         if region in self.puzzle.pythonized_constraints:
#             # check if it is the correct size for surjective logic
#             if self.puzzle.pythonized_constraints[region][0] != 'UniqueSet':
#                 raise CommandError(f'Can not do support_cases on region {region}')
#             cells = self.puzzle.pythonized_constraints[region][1]

#             if len(cells) != len(self.puzzle.symbols_python):
#                 raise CommandError("can't do surjective logic on a unique set that isn't the same size as symbols")
#             qualified_region_name = f'(region_full_locked_set H.{region})'
#         else:
#             for var in self.current.proof_state.goals[0].variables:
#                 if var.name == region:
#                     break
#             else:
#                 print('could not find a region by that name in the context')
#             # TODO for now, assume that it starts with forall f in S
#             qualified_region_name = f'{region} f hf'
#         self.tactic(f'let h := {qualified_region_name}')

#         yield from self.support_cases('h',digit)

#     def rfl(self) -> Generator[str,str,None]:
#         self.tactic('rfl')
#         return
#         yield
    
#     def exact(self,hypothesis: str) -> Generator[str,str,None]:
#         self.tactic(f'exact {hypothesis}')
#         return
#         yield

#     def naked_single(self,cell: int) -> Generator[str,str,None]:
#         # first find the digit to fill (check that all digits but one are eliminated)
#         if cell not in self.current.eliminations:
#             # definetely not able to eliminate the candidates
#             raise CommandError(f'cell {cell} has more than one candidate, can not do naked_single')
#         elims = self.current.eliminations[cell]
            
#         not_eliminated = None
#         for digit in self.puzzle.symbols_python:
#             if digit in elims:
#                 continue
#             # not eliminated
#             if not_eliminated is None:
#                 not_eliminated = digit
#             else:
#                 # there is more than one candidate
#                 # can not do naked single
#                 raise CommandError(f'cell {cell} has more than one candidate, can not do naked_single')
        
#         if not_eliminated is None:
#             # this cell has no candidates, solve using cell_cases instead
#             raise CommandError(f'cell {cell} has no candidates, this should be solved by cell_cases')
#         digit = not_eliminated
        
#         # naked single macro. fills the cell with the digit by doing cases on that cell
#         yield from self.fill(cell,digit,self.cell_cases(cell,{digit: self.rfl()}))

#     def finish(self):
#         """Where all the digits are known, this function finishes out the proof.
#         This finishes out the proof by 
#         - creating the function g, 
#         - proving it satisfies all constraints (which could need some proof help, but most of it should be automatic)
#         - showing that it is the only function using all the proofs of each digit that were created in the solving process"""

#         # going to be using it a lot, so local variable
#         grid = self.current.grid


#         if any([x is None for x in grid]):
#             # not all digits are known.
#             raise CommandError('Not all digits are solved, can not finish proof')
        
#         self.tactic(f'theorem SolvePuzzle {{S : Set (Nat → {self.puzzle.symbols})}} (H : ∀ f, f ∈ S ↔ Puzzle f): ∃! (g: Nat -> {self.puzzle.symbols}), g ∈ S := by')
#         self.proof_level += 1

#         # create the function g and use it
#         # using the digits proved to create the function
#         self.tactic(
# f"""let digits: Array {self.puzzle.symbols} := #{str(grid).replace("'","")}
# -- for use later, say how long it is
# have len: digits.size = {len(grid)} := by decide
# -- define the function g and use it
# let g : Nat → {self.puzzle.symbols} := fun x => digits[x]? |>.getD {self.puzzle.symbols_python[0]}
# use g
# constructor -- splits into testing constraints and uniqueness
# · simp only
#   apply (H g).mpr""")
#         self.proof_level += 1
#         # next is to prove that obeys the constraints of the puzzle
#         # this is done by splitting up the structure
#         # at this point it is all hard coded to the specific puzzle
#         # later there will be functions to prove UniqueSet constraints, theromemeters, etc.
#         self.tactic(
# """constructor
# · -- outside the grid
#   intro n hn
#   unfold g
#   conv => enter [1, 1]; apply Array.getElem?_eq_none (by {rw [len]; assumption})
#   simp"""
#         )
#         self.proof_level += 1
#         # this relies on the order of .items() and values() being consistent, we can change data structures to a list or something if that ends up not being true
#         for _, constraint in self.puzzle.top_level_constraints():
#             self.place_dot()
#             if re.match(r'f\s+\d+\s*=\s*\d',constraint):
#                 self.tactic("decide")
#             elif constraint.startswith('UniqueSet'):
#                 self.tactic('apply injOn_by_card; decide')
#             else:
#                 match constraint:
#                     case "NormalSudoku f":
#                         self.tactic("constructor; iterate 27 apply injOn_by_card; decide")
#                     case _:
#                         raise ValueError(f'do not know how to prove the constraint {constraint}')

#         self.proof_level -= 1
#         # uniqueness start here
#         self.place_dot()
#         self.tactic(
# f"""intro h hh
# replace H := (H h).mp hh
# ext x
# by_cases xin: x < {len(grid)}
# · interval_cases x"""
#         )
#         self.proof_level += 2
#         # now to get the proof for each cell
#         for cell in range(len(grid)):
#             self.place_dot()
#             self.tactic(f'exact (c{cell} H)')
#         self.proof_level -= 1
#         # and handle the outside the grid normalization
#         self.place_dot()
#         self.tactic(
# f"""rw [H.outside_grid]
# · unfold g
#   simp at xin
#   conv => enter [2,1]; apply Array.getElem?_eq_none (by {{rw [len]; assumption}})
#   simp
# push_neg at xin
# apply xin"""
#         )
#         _, diags = self._send_proof()

#         self.proof_level -= 3
        
#         # proof complete
#         # print(self.repl.full_text)

#         if not diags:
#             return
#         for diag in diags:
#             print('Lean diag level',diag['severity'])
#             print(diag['fullRange'],diag['range'])
#             print(diag['message'])

#         raise Exception()


#     def handle_input(self, cmd: str) -> Generator[str,str,None]:
#         if cmd == '':
#             raise CommandError("No command given")
#         args = cmd.split()
#         name = args[0]
#         params = args[1:]
#         if name == 'exit':
#             # ignores all arguments
#             exit(0)
#         elif name == 'fill':
#             if len(params) != 2:
#                 raise CommandError("expected 'fill cell digit'")
#             try:
#                 cell = int(params[0])
#                 digit = int(params[1])
#             except ValueError:
#                 raise CommandError('digit and cell must be integers')
#             if not (0 <= cell < self.puzzle.cell_count):
#                 raise CommandError(f'cell {cell} out of range')
#             if digit not in self.puzzle.symbols_python:
#                 raise CommandError(f'digit {digit} invalid')
#             yield from self.fill(cell,digit)
#         elif name == 'have':
#             # the rest of the line is the goal
#             goal = cmd.removeprefix('have').strip()
#             if goal == "":
#                 raise CommandError("expected 'have [goal]'")
#             yield from self.have('h',goal)
#         elif name == 'cell_cases':
#             if len(params) != 1:
#                 raise CommandError("expected 'cell_cases cell'")
#             try:
#                 cell = int(params[0])
#             except ValueError:
#                 raise CommandError('cell must be an integer')
#             if not (0 <= cell < self.puzzle.cell_count):
#                 raise CommandError(f'cell {cell} out of range')
#             yield from self.cell_cases(cell)
#         elif name == 'support_cases':
#             if len(params) != 2:
#                 raise CommandError("expected 'support_cases region digit'")
#             region = params[0]
#             try: 
#                 digit = int(params[1])
#             except ValueError:
#                 raise CommandError('digit must be an integer')
#             if digit not in self.puzzle.symbols_python:
#                 raise CommandError(f'digit {digit} invalid')
#             yield from self.support_cases_manual(digit, region)
#         elif name == 'rfl':
#             if len(params) != 0:
#                 raise CommandError("expected 'rfl' with no arguments")
#             yield from self.rfl()
#         elif name == 'exact':
#             if len(params) != 1:
#                 raise CommandError("expected 'exact hypothesis'")
#             yield from self.exact(params[0])
#         elif name == 'naked_single':
#             if len(params) != 1:
#                 raise CommandError("expected 'naked_single cell")
#             try:
#                 cell = int(params[0])
#             except ValueError:
#                 raise CommandError('cell must be an integer')
#             if not (0 <= cell < self.puzzle.cell_count):
#                 raise CommandError(f'cell {cell} out of range')
#             yield from self.naked_single(cell)
#         elif name == 'finish':
#             if len(params) != 0:
#                 raise CommandError('finish takes no args')
#             self.finish()
#         else:
#             raise CommandError(f'unknown command {name}')

    def controller(self) -> Generator[str,str,None]:
        """main logic loop for cli"""
        while True:
            cmd = yield ''
            try:
                yield from self.handle_input(cmd)
            except CommandError as e:
                print(f'[!] {e}')
    

    @contextmanager
    def subproof(self):
        if self.is_reconstructing:
            yield
            return
        
        # get the index of where the sub-proof starts
        start_index = len(self.journal)
        snapshot = self.current.copy()

        try:
            # give control to the caller
            yield
            # done, lets commit the subproof
            steps = self.journal.pop_subproof(start_index)
            # figure out the goal of the subproof
            ????
            # create the delta
            delta = Delta(list(steps.commands()),steps.lean_code_file(),)
            # append it to the journal
            self.journal.add(delta)
            # update the current state
            self.current = snapshot
            snapshot.add_delta(delta)

        except Exception as e:
            # deal with errors
            raise e

    def undo(self):
        # just get rid of the last command
        try:
            self.journal.pop()
        except ValueError:
            raise CommandError('no steps to undo')
        
        # recreate the world
        self.reconstruct()


    def reconstruct(self):
        # find the latest top level snapshot
        self.current = State() # TODO, this just always chooses initial, it should take the most recent top level snapshot
        self._active_gen = self.controller()
        self.terminal_prompt = next(self._active_gen)

        self.is_reconstructing = True

        for command in self.journal.commands():
            self.terminal_prompt = self._active_gen.send(command)

        # after this proocess, _active_gen is in the correct position
        self.is_reconstructing = False

    def command(self,cmd:str):
        # print(cmd)
        self.terminal_prompt = self._active_gen.send(cmd)
        return self.terminal_prompt
