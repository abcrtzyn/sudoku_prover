
from contextlib import contextmanager
from dataclasses import dataclass
import functools
import re
from typing import Any, Callable, Concatenate, Dict, Generator, List, ParamSpec, Tuple, cast

from sudoku_prover_ui.file_exporter import export_file
from sudoku_prover_ui.journal import Delta, Journal, State
from sudoku_prover_ui.lean_repl import LeanLspRepl
from sudoku_prover_ui.puzzle import Puzzle

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

@dataclass
class CloseSubproofInfo:
    start_delta: int
    start_snapshot: State
    grid_changes: Dict[int,int]
    elimination_changes: Dict[int,Dict[int,Tuple[str,Any]]]


P = ParamSpec("P")
ProofGenerator = Generator[str | CommandError,'ProofGenerator',None]
ValidateFunc = Callable[[],None]
RunFunc = Callable[[],ProofGenerator|None]
CommandTemplate = Generator[ValidateFunc,None,RunFunc]

class ProofEngine:

    def __enter__(self):
        return self.setup()
    
    def close(self):
        self.repl.close()

    def __exit__(self, *args): # pyright: ignore[reportMissingParameterType, reportUnknownParameterType]
        self.close()

    def __init__(self, puzzle: Puzzle):
        self.repl = LeanLspRepl(REPO_ROOT) # pyright: ignore[reportArgumentType]
        self.puzzle = puzzle
        self._active_gen: ProofGenerator
        self.terminal_prompt: str
        self.journal: Journal = Journal(None)
        self.prepared_text = ''
        self.prepared_grid_changes: Dict[int,int] = {}
        self.prepared_elimination_changes: Dict[int,Dict[int,Tuple[str,Any]]] = {}
        # this keeps track of what level of proof we are on, it also determines how much indent there is
        # indent is 2*proof_level
        # any lemma or have block increases this by one, also any cases will but with the exception of the center dots
        self.proof_level = 0
        self._place_dot: bool = False
        self.no_commit_flag: int = 0
        self.close_subproof: CloseSubproofInfo | None = None
        # generating is the generator rollback safety flag
        # if it is False, then no changes have been made to the state, we can safely enter another command without issue
        # if it is True, any errors must crash because they have modified the state of the active generator.
        # note that the active generator is the hardest part to rollback from, the prepared changes variables are super easy to clear.
        # eventually it can be possible to rollback using undo reconstruct logic
        # also see command_flow
        self.generating: bool = True

    def setup(self):
        self.repl.open()

        self.current = State([None] * self.puzzle.cell_count)

        try:
            # imports
            import_text = ''
            for imp in ['Mathlib.Tactic.IntervalCases','SudokuProverLogic.Basic',
                        f'SudokuProverLogic.{self.puzzle.symbols}','SudokuProverLogic.Tactics'] + self.puzzle.lean_imports:
                import_text += f'import {imp}\n'
            
            self.tactic(import_text)
            self.command_internal('imports')
            self.journal.protected_steps += 1
            
            # set options, maybe we will format how lean wants later, but I don't care
            options_text = 'set_option linter.style.whitespace false\nset_option linter.style.longLine false\n'
            self.tactic(options_text)
            self.command_internal('lint options')
            self.journal.protected_steps += 1

            # give the puzzle to Lean
            puzzle_text = self.puzzle.generate_lean_structure()
            self.tactic(puzzle_text)
            self.command_internal('puzzle def')
            self.journal.protected_steps += 1
            
            # start with any initial constraints, might just be given digits
            # anything that I would consider part of the solution that is given gets processed here
            for name, constraint in self.puzzle.pythonized_constraints.items():
                match constraint[0]:
                    case 'Given':
                        cell = constraint[1][0]
                        digit = constraint[1][1]
                        self.tactic(f"lemma c{cell} {{f: Nat -> {self.puzzle.symbols}}} (P: Puzzle f): f {cell} = {digit} := P.{name}")
                
                        # create elimination proofs for each
                        self.prepared_grid_changes[cell] = digit
                        self.region_eliminate(cell,digit,f'c{cell}')
                    case 'UniqueSet':
                        pass
                    case _:
                        raise NotImplementedError(f'constraint of type {constraint[0]} has no implementation for initialization')
            
            # get a new line in there for spacing reasons
            self.tactic('')
            self.command_internal('intialize constraints')
            self.journal.protected_steps += 1
                    
            self._active_gen = self.main()
            result = next(self._active_gen)
            if isinstance(result, CommandError):
                raise result
            self.terminal_prompt = result
        except:
            self.close()
            raise

        return self


    """The functions that make this whole thing work"""

    def commit(self,cmd: str, proof_state: List[str]):
        """Commit work to the journal and update state"""
        delta = Delta([cmd],self.prepared_text,self.prepared_grid_changes,self.prepared_elimination_changes)
        self.journal.add(delta)
        self.current.add_delta(delta,proof_state)
        self.prepared_text = ''
        self.prepared_grid_changes = {}
        self.prepared_elimination_changes = {}
        self.generating = False

    def command(self,cmd:str):
        """user input function, given a command, gives it to the active proof generator,
        returns with the next user propmt"""
        if cmd == '':
            print('no command given, no action taken')
            return
        args = cmd.split()
        name = args[0]
        params = args[1:]

        # find the right command
        proof_gen: ProofGenerator | None = None
        try:
            match name:
                case 'exit':
                    exit(0)
                case 'save':
                    if len(params) != 1:
                        print('expected "save filepath"')
                        return
                    export_file(params[0],self.puzzle,self.journal.export_commands())
                    return
                case 'undo':
                    raise NotImplementedError('undo is not implemented yet')
                # done with cli commands, now for regular commands
                case 'fill':
                    if len(params) != 2:
                        raise CommandError("expected 'fill cell digit'")
                    try:
                        cell = int(params[0])
                        digit = int(params[1])
                    except ValueError:
                        raise CommandError('digit and cell must be integers')
                    proof_gen = self.fill(cell,digit)
                case 'have':
                    # the rest of the line is the goal
                    goal = cmd.removeprefix('have').strip()
                    if goal == "":
                        raise CommandError("expected 'have [goal]'")
                    proof_gen = self.have('h',goal)
                case 'cell_cases':
                    if len(params) != 1:
                        raise CommandError("expected 'cell_cases cell'")
                    try:
                        cell = int(params[0])
                    except ValueError:
                        raise CommandError('cell must be an integer')
                    proof_gen = self.cell_cases(cell)
                # case 'support_cases':
                #     if len(params) != 2:
                #         raise CommandError("expected 'support_cases region digit'")
                #     region = params[0]
                #     try: 
                #         digit = int(params[1])
                #     except ValueError:
                #         raise CommandError('digit must be an integer')
                #     if digit not in self.puzzle.symbols_python:
                #         raise CommandError(f'digit {digit} invalid')
                #     self.support_cases_manual(digit, region)
                case 'rfl':
                    if len(params) != 0:
                        raise CommandError("expected 'rfl' with no arguments")
                    proof_gen = self.rfl()
                case 'exact':
                    if len(params) != 1:
                        raise CommandError("expected 'exact hypothesis'")
                    proof_gen = self.exact(params[0])
                case 'naked_single':
                    if len(params) != 1:
                        raise CommandError("expected 'naked_single cell")
                    try:
                        cell = int(params[0])
                    except ValueError:
                        raise CommandError('cell must be an integer')
                    proof_gen = cast(ProofGenerator,self.naked_single(cell)) # pyright: ignore[reportUnknownMemberType]
                case 'finish':
                    if len(params) != 0:
                        raise CommandError('finish takes no args')
                    proof_gen = self.finish()
                case _:
                        raise CommandError('unknown command')
        except CommandError as e:
            print(e)
            return

        assert proof_gen is not None, 'command parsing match case passed without assigning function, it must set func, or throw an error'

        try:
            result = self._active_gen.send(proof_gen)
            if isinstance(result, CommandError):
                raise result
            self.terminal_prompt = result
        except CommandError as e:
            print(e)
            # this is a safe error
            return
        except Exception:
            print('non-command-error in command processing or text creation')
            raise

        try:
            goals, _ = self.repl.check_code(self.current.lean_file + self.prepared_text)
            
        except Exception:
            print('error in execution')
            raise
        # this code is good, lets commit it
        self.commit(cmd, goals)

        # collapse any subproofs that need to be collapsed
        if self.close_subproof is not None:
            start_delta = self.close_subproof.start_delta
            pre_subproof_state = self.close_subproof.start_snapshot
            subproof_grid_changes = self.close_subproof.grid_changes
            subproof_elimination_changes = self.close_subproof.elimination_changes

            proof = self.journal.pop_subproof(start_delta)
            cmds = list(proof.commands())
            code = proof.lean_code_file()
            proof_state = self.current.proof_state
            delta = Delta(cmds,code,subproof_grid_changes,subproof_elimination_changes)
            self.journal.add(delta)
            self.current = pre_subproof_state
            self.current.add_delta(delta,proof_state)

            self.close_subproof = None
        
        return self.terminal_prompt

    def command_internal(self,cmd:str):
        """internal run prepared and commit, used for setup and such"""
        goals, _ = self.repl.check_code(self.current.lean_file + self.prepared_text)
        self.commit(cmd,goals)

    def main(self) -> Generator[str|CommandError,ProofGenerator,None]:
        """top level proof"""
        while True:
            gen = yield ''
            while True:
                try:
                    yield from gen
                    break
                except CommandError as e:
                    gen = yield e


    @staticmethod
    def command_flow(func: Callable[Concatenate['ProofEngine',P], CommandTemplate]) -> Callable[Concatenate['ProofEngine',P],ProofGenerator]:
        """command flow is the wrapper that creates a whole bunch of safety logic
        every text generating command must use this to ensure that clean rollback is possible
        I suggest looking at example functions, but basically every command must
        - yield a validate function that checks that the user provided arguments are valid
        - yield a run function that makes changes to prepared variables like lean_code and grid_changes
        If your generator is being run by a macro that has already validated the arguments (is in generating mode), the validate function will be skipped.
        Any calculation and validation can occur in top level in the function, but it will be subject to the execution status ProofEngine.generating.
        """

        @functools.wraps(func)
        def wrapper(_self: 'ProofEngine', *args: P.args, **kwargs: P.kwargs) -> ProofGenerator:
            
            setup_gen = func(_self, *args, **kwargs)
            # get the user input validate function
            try:
                validate_func = next(setup_gen)
            except StopIteration:
                # the developer did not yield a validate function
                raise Exception("Command must yield a validate function.")
            except CommandError as e:
                # if command error happened, the developer raised a command error and they shouldn't have
                raise Exception('function should not raise a CommandError, it is reserved for internal use', e)
            except Exception as e:
                # the top level function code raised an error, raise it as a command error if we aren't generating yet
                if not _self.generating:
                    raise CommandError(e)
                # else, raise normally
                raise

            # do user input validation
            if not _self.generating:
                try:
                    validate_func()
                except CommandError as e:
                    raise Exception('validate should not raise a CommandError, it is reserved for internal use', e)
                except Exception as e:
                    # Top-level code didn't run yet, so it's safe to wrap
                    raise CommandError(e)

            # get the run function from the return of the generator
            try:
                # expecting stop iteration or any other error
                next(setup_gen)
            except StopIteration as e:
                run_func = cast(RunFunc,e.value)
            except CommandError as e:
                # if command error happened, the developer raised a command error and they shouldn't have
                raise Exception('function should not raise a CommandError, it is reserved for internal use', e)
            except Exception as e:
                # the top level function code raised an error, raise it as a command error if we aren't generating yet
                if not _self.generating:
                    raise CommandError(e)
                # else, raise normally
                raise
            else:
                raise RuntimeError("Command must return with the run function, not yield another value")

            _self.generating = True
            # execute, run the function, or yield from the generator, any errors here are passed down
            if gen := run_func():
                yield from gen
        
        return wrapper



    @contextmanager
    def subproof(self):
        if self.no_commit_flag > 0:
            # I think this will just store the subproof changes
            # run the subproof commands to get the code
            # and then restore the changes
            subproof_grid_changes = self.prepared_grid_changes
            subproof_elimination_changes = self.prepared_elimination_changes
            self.prepared_grid_changes = {}
            self.prepared_elimination_changes = {}
            try:
                yield
            finally:
                self.prepared_grid_changes = subproof_grid_changes
                self.prepared_elimination_changes = subproof_elimination_changes
            # done
        else:
            # get the starting index of the subproof
            pre_subproof_state = self.current.copy()
            start_delta = len(self.journal)
            subproof_grid_changes = self.prepared_grid_changes
            subproof_elimination_changes = self.prepared_elimination_changes
            self.prepared_grid_changes = {}
            self.prepared_elimination_changes = {}
            try:
                yield
            finally:
                self.close_subproof = CloseSubproofInfo(start_delta,pre_subproof_state,subproof_grid_changes,subproof_elimination_changes)


    def do_subproof(self, prompt: str) -> ProofGenerator:
        with self.subproof():
            # go get a command to run, TODO or take from parameters
            gen = yield prompt
            while True:
                try:
                    yield from gen
                    break
                except CommandError as e:
                    gen = yield e

    def place_dot(self):
        self._place_dot = True

    @contextmanager
    def indent(self):
        """Increments proof level, and decrements after."""
        self.proof_level += 1
        try:
            yield
        finally:
            self.proof_level -= 1

    def tactic(self, tactic: str):
        """adds text to the prepared text variable with a potential dot."""

        tactic_text = ''
        for line in tactic.splitlines(True):
            tactic_text += f'{'  '*(self.proof_level-self._place_dot)}{'· ' if self._place_dot else ''}{line}'
            self._place_dot = False

        # print(tactic_text)
        self.prepared_text += tactic_text + '\n'
        

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

    def region_eliminate(self, cell: int,digit: int,proof_name:str):
        """eliminates all of digit from every cell in every region that cell is a part of"""
        for name, constraint in self.puzzle.pythonized_constraints.items():
            if constraint[0] != 'UniqueSet':
                continue
            if cell in constraint[1]:
                for i in constraint[1]:
                    if i == cell:
                        continue        
                    # we have a choice to override a current elimination rule, or keep the first one
                    # there are pros and cons to either, but that is for future me to decide.
                    # this code OVERRIDES existing elemination rules
                    if i not in self.prepared_elimination_changes:
                        self.prepared_elimination_changes[i] = dict()
                    self.prepared_elimination_changes[i][digit] = ('digit_in_region', (cell,name,proof_name))


    def generate_elimination_proof(self,cell: int, digit: int, hypothesis: str):
        """Given the current cell and digit and hypothesis name to eliminate
        eliminates this contradictory case"""
        
        if self.current.grid[cell] is not None:
            proof = f'exact digit_in_cell {hypothesis} (c{cell} P)'
            self.tactic(f'exfalso; {proof}')
        elif cell in self.current.eliminations and digit in self.current.eliminations[cell]:
            elim = self.current.eliminations[cell][digit]
            if elim[0] == 'digit_in_region':
                proof = f'exact digit_in_region {hypothesis} P.{elim[1][1]} ({elim[1][2]} P)'
            else:
                print('unknown elimination reason',elim[0])
                exit(4)
            self.tactic(f'exfalso; {proof}')
        else:
            print(f'no elimination present for {cell} {digit}')
            exit(5)

    @command_flow
    def have(self, name: str, goal: str):
        """generates a have goal in Lean, can be anything at this point, there will be rules later..."""
 
        yield lambda: None

        def run() -> ProofGenerator:
            # if it is a top level goal, need to start a new lemma, otherwise do a have statement
            if self.proof_level == 0:
                self.tactic(f"lemma {name} {{f: Nat -> {self.puzzle.symbols}}} (P: Puzzle f): {goal} := by")
            else:
                self.tactic(f"have {name}: {goal} := by")
            with self.indent():
                yield from self.do_subproof(goal)
                
            if self.proof_level == 0:
                # add a newline for top level goals.
                self.tactic('')

        return run
        
    @command_flow
    def fill(self, cell: int, digit: int):
        """special case to fill a cell with a digit, creates the goal and after is proved, adds it to the datastructures and creates eliminations"""

        def validate():
            if not (0 <= cell < self.puzzle.cell_count):
                raise ValueError(f'cell {cell} out of range')
            if digit not in self.puzzle.symbols_python:
                raise ValueError(f'digit {digit} invalid')

        yield validate

        def run() -> ProofGenerator:
            # set up what changes will occur after the subproof
            self.prepared_grid_changes[cell] = digit
            self.region_eliminate(cell,digit,f'c{cell}')

            yield from self.have(f'c{cell}', f'f {cell} = {digit}')
            
        return run
    

    @command_flow
    def cell_cases(self, cell: int):

        def validate():
            if not (0 <= cell < self.puzzle.cell_count):
                raise ValueError(f'cell {cell} out of range')

        yield validate

        def run() -> ProofGenerator:
            self.tactic(f'cases h: f {cell}')
            
            with self.indent():
                # we know the order of these cases, it's exactly the order of the symbols
                for digit in self.puzzle.symbols_python:
                    self.place_dot()
                    if cell in self.current.eliminations and digit in self.current.eliminations[cell]:
                        self.generate_elimination_proof(cell,digit,'h')
                        # TODO we also need to check for accepting cases, not yet
                    else:
                        yield from self.do_subproof(f'cell_cases {digit}')
        
        return run
            

# #     def support_cases(self, hypothesis: str, digit: int | None, commands: Dict[int,Generator[str,str,None]] | None = None) -> Generator[str,str,None]:
# #         """Does support_cases or locked_support_cases on the hypothesis and digit
# #         the hypothesis is must be of the form SupportSet {...} n or LockedSet {...} {...}
# #         This function will detect which one is needed. If the hypothesis is a locked set, a digit must be given"""
# #         for var in self.current.proof_state.goals[0].variables:
# #             if var.name == hypothesis:
# #                 break
# #         else:
# #             print(f'could not find a hypothesis {hypothesis} in the context')
# #             exit(2)
# #         pattern = r'(?P<type>Locked|Support)Set f \{(?P<data>\d+(?:,\s*\d+)*)\} (?P<digit>\S|.+)'
# #         mat = re.match(pattern, var.t)
# #         if mat is None:
# #             print(f'{var.t} did not match the re')
# #             exit(7)
# #         region_is_locked = mat.group('type') == 'Locked'
# #         cell_set = [int(x.strip()) for x in mat.group('data').split(',')]
# #         # if it is a support set, get the digit from the hypothesis
# #         if not region_is_locked:
# #             digit = int(mat.group('digit'))
        
# #         if digit is None:
# #             print('no digit provided for locked set')
# #             exit(8)
# #         self.tactic(f"""{'locked_support_cases' if region_is_locked else 'support_cases'} h {digit}""")
# #         with self.indent():
# #             for cell in cell_set:
# #                 self.place_dot()
# #                 if (self.current.grid[cell] is not None) or (cell in self.current.eliminations and digit in self.current.eliminations[cell]):
# #                     self.generate_elimination_proof(cell,digit,'h')
# #                 # TODO we also need to check for accepting cases, not yet
# #                 else:
# #                     yield from self._execute_dict_or_prompt(commands,cell,f'support_cases {cell}')
            
        
# #     def support_cases_manual(self, digit: int, region: str) -> Generator[str,str,None]:
# #         # couple things we have to do in order to call support cases
# #         # one, create the hypothesis to run cases on, which has many cases
# #         # is there a hypothesis by that name in the context?
# #         qualified_region_name = None
# #         if region in self.puzzle.pythonized_constraints:
# #             # check if it is the correct size for surjective logic
# #             if self.puzzle.pythonized_constraints[region][0] != 'UniqueSet':
# #                 raise ValueError(f'Can not do support_cases on region {region}')
# #             cells = self.puzzle.pythonized_constraints[region][1]

# #             if len(cells) != len(self.puzzle.symbols_python):
# #                 raise ValueError("can't do surjective logic on a unique set that isn't the same size as symbols")
# #             qualified_region_name = f'(region_full_locked_set H.{region})'
# #         else:
# #             for var in self.current.proof_state.goals[0].variables:
# #                 if var.name == region:
# #                     break
# #             else:
# #                 print('could not find a region by that name in the context')
# #             # TODO for now, assume that it starts with forall f in S
# #             qualified_region_name = f'{region} f hf'
# #         self.tactic(f'let h := {qualified_region_name}')

# #         yield from self.support_cases('h',digit)

    @command_flow
    def rfl(self):
        yield lambda: None

        def run():
            self.tactic('rfl')
            return

        return run
    
    @command_flow
    def exact(self,hypothesis: str):
        yield lambda: None
        
        def run():
            self.tactic(f'exact {hypothesis}')
            return

        return run

    @command_flow
    def naked_single(self,cell: int):

        def validate():
            if not (0 <= cell < self.puzzle.cell_count):
                raise ValueError('naked_single cell must be an index from 0 to cell_count')
            
        yield validate

        # first find the digit to fill (check that all digits but one are eliminated)
        if cell not in self.current.eliminations:
            # definetely not able to eliminate the candidates
            raise ValueError(f'cell {cell} has more than one candidate, can not do naked_single')
        elims = self.current.eliminations[cell]
            
        not_eliminated = None
        for digit in self.puzzle.symbols_python:
            if digit in elims:
                continue
            # not eliminated
            if not_eliminated is None:
                not_eliminated = digit
            else:
                # there is more than one candidate
                # can not do naked single
                raise ValueError(f'cell {cell} has more than one candidate, can not do naked_single')
        
        if not_eliminated is None:
            # this cell has no candidates, solve using cell_cases instead
            raise ValueError(f'cell {cell} has no candidates, this should be solved by cell_cases')
        digit = not_eliminated
        
        
        def run() -> None:
            self.no_commit_flag += 1
            # naked single macro. fills the cell with the digit by doing cases on that cell
            # yield from self.fill(cell,digit,self.cell_cases(cell,{digit: self.rfl()}))
            # for right now, this function has to has to handle the genartors itself
            gen = self.fill(cell,digit)
            _ = next(gen)
            _ = gen.send(self.cell_cases(cell))
            try:
                _ = gen.send(self.rfl())
            except StopIteration:
                pass
            
            self.no_commit_flag -= 1

            return
        
        return run


    @command_flow
    def finish(self):
        """Where all the digits are known, this function finishes out the proof.
        This finishes out the proof by 
        - creating the function g, 
        - proving it satisfies all constraints (which could need some proof help, but most of it should be automatic)
        - showing that it is the only function using all the proofs of each digit that were created in the solving process"""
        
        # going to be using it a lot, so local variable
        grid = self.current.grid
        
        def validate():
            if any([x is None for x in grid]):
                # not all digits are known.
                raise ValueError('Not all digits are solved, can not finish proof')
        
        yield validate

        def run() -> None:
            self.tactic(f'theorem SolvePuzzle {{S : Set (Nat → {self.puzzle.symbols})}} (H : ∀ f, f ∈ S ↔ Puzzle f): ∃! (g: Nat -> {self.puzzle.symbols}), g ∈ S := by')
            self.proof_level += 1

            # create the function g and use it
            # using the digits proved to create the function
            self.tactic(
f"""let digits: Array {self.puzzle.symbols} := #{str(grid).replace("'","")}
-- for use later, say how long it is
have len: digits.size = {len(grid)} := by decide
-- define the function g and use it
let g : Nat → {self.puzzle.symbols} := fun x => digits[x]? |>.getD {self.puzzle.symbols_python[0]}
use g
constructor -- splits into testing constraints and uniqueness
· simp only
  apply (H g).mpr""")
            self.proof_level += 1
            # next is to prove that obeys the constraints of the puzzle
            # this is done by splitting up the structure
            # at this point it is all hard coded to the specific puzzle
            # later there will be functions to prove UniqueSet constraints, theromemeters, etc.
            self.tactic(
"""constructor
· -- outside the grid
  intro n hn
  unfold g
  conv => enter [1, 1]; apply Array.getElem?_eq_none (by {rw [len]; assumption})
  simp"""
            )
            self.proof_level += 1
            # this relies on the order of .items() and values() being consistent, we can change data structures to a list or something if that ends up not being true
            for _, constraint in self.puzzle.top_level_constraints():
                self.place_dot()
                if re.match(r'f\s+\d+\s*=\s*\d',constraint):
                    self.tactic("decide")
                elif constraint.startswith('UniqueSet'):
                    self.tactic('apply injOn_by_card; decide')
                else:
                    match constraint:
                        case "NormalSudoku f":
                            self.tactic("constructor; iterate 27 apply injOn_by_card; decide")
                        case _:
                            raise ValueError(f'do not know how to prove the constraint {constraint}')

            self.proof_level -= 1
            # uniqueness start here
            self.place_dot()
            self.tactic(
f"""intro h hh
replace H := (H h).mp hh
ext x
by_cases xin: x < {len(grid)}
· interval_cases x"""
            )
            self.proof_level += 2
            # now to get the proof for each cell
            for cell in range(len(grid)):
                self.place_dot()
                self.tactic(f'exact (c{cell} H)')
            self.proof_level -= 1
            # and handle the outside the grid normalization
            self.place_dot()
            self.tactic(
f"""rw [H.outside_grid]
· unfold g
  simp at xin
  conv => enter [2,1]; apply Array.getElem?_eq_none (by {{rw [len]; assumption}})
  simp
push_neg at xin
apply xin"""
            )

            self.proof_level -= 3


            # proof complete
            # print(self.repl.full_text)

            # if not diags:
            #     return
            # for diag in diags:
            #     print('Lean diag level',diag['severity'])
            #     print(diag['fullRange'],diag['range'])
            #     print(diag['message'])

            # raise Exception()
            return


        return run
    

# Undo should be within reach.
# I belive the issue we will run into is that we still need to update state (even in collapsed subproofs)
# so that the commands know what they are dealing with
# This will be true for all macro commands, including naked_single, even if it doesn't matter as much
# There will have to be commits to change grid state, and the user command level commits to change the user commands and lean code


#     def undo(self):
#         # just get rid of the last command
#         try:
#             self.journal.pop()
#         except ValueError:
#             raise RuntimeError('no steps to undo')
        
#         # recreate the world
#         self.reconstruct()

#     def reconstruct(self):
#         # find the latest top level snapshot
#         self.current = State() # TODO, this just always chooses initial, it should take the most recent top level snapshot
#         self._active_gen = self.controller()
#         self.terminal_prompt = next(self._active_gen)

#         self.is_reconstructing = True

#         for command in self.journal.commands():
#             self.terminal_prompt = self._active_gen.send(command)

#         # after this proocess, _active_gen is in the correct position
#         self.is_reconstructing = False

#         # recreate the current state
#         self.current.add_journal(self.journal)
#         # update the lean server too
#         goals, _ = self.repl.check_code(self.current.lean_file)
#         # keep the proof state
#         self.current.proof_state = goals
