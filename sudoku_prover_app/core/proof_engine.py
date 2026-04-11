
from contextlib import contextmanager
from dataclasses import dataclass
import functools
import re
from typing import Any, Callable, Concatenate, Dict, Generator, List, ParamSpec, Tuple, cast

from sudoku_prover_app.tactics.basic_tactics import cell_cases, exact, fill, have, naked_single, region_eliminate, rfl
from sudoku_prover_app.io.file_exporter import export_file
from sudoku_prover_app.core.journal import Delta, Journal, State
from sudoku_prover_app.core.lean_repl import LeanLspRepl
from sudoku_prover_app.core.puzzle import Puzzle

from pathlib import Path

# __file__ is .../sudoku_prover_app/proof_engine.py
# .parent is .../sudoku_prover_app/
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
    @property
    def prepared_text(self) -> str:
        return self._prepared_text
    @prepared_text.setter
    def prepared_text(self, value: str):
        if not self.generating:
            raise RuntimeError("State Mutation Error: Attempted to modify 'prepared_text' outside of generating mode.")
        self._prepared_text = value

    @property
    def prepared_grid_changes(self) -> Dict[int,int]:
        return self._prepared_grid_changes

    @prepared_grid_changes.setter
    def prepared_grid_changes(self, value: Dict[int,int]):
        
        if not self.generating:
            raise RuntimeError("State Mutation Error: Attempted to modify 'prepared_grid_changes' outside of generating mode.")
        self._prepared_grid_changes = value

    @property
    def prepared_elimination_changes(self) -> Dict[int,Dict[int,Tuple[str,Any]]]:
        return self._prepared_elimination_changes

    @prepared_elimination_changes.setter
    def prepared_elimination_changes(self, value: Dict[int,Dict[int,Tuple[str,Any]]]):
        if not self.generating:
            raise RuntimeError("State Mutation Error: Attempted to modify 'prepared_elimination_changes' outside of generating mode.")
        self._prepared_elimination_changes = value



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
        self.prepared_text = ''
        self.prepared_grid_changes = {}
        self.prepared_elimination_changes = {}

    def setup(self):
        self.repl.open()

        self.current = State([None] * self.puzzle.cell_count)

        try:
            self.generating = True
            # imports
            import_text = ''
            for imp in ['Mathlib.Tactic.IntervalCases','SudokuProverLogic.Basic',
                        f'SudokuProverLogic.{self.puzzle.symbols}','SudokuProverLogic.Tactics'] + self.puzzle.lean_imports:
                import_text += f'import {imp}\n'
            
            self.tactic(import_text)
            self.command_internal('imports')
            self.journal.protected_steps += 1
            self.generating = True

            # set options, maybe we will format how lean wants later, but I don't care
            options_text = 'set_option linter.style.whitespace false\nset_option linter.style.longLine false\n'
            self.tactic(options_text)
            self.command_internal('lint options')
            self.journal.protected_steps += 1
            self.generating: bool = True
            
            # give the puzzle to Lean
            puzzle_text = self.puzzle.generate_lean_structure()
            self.tactic(puzzle_text)
            self.command_internal('puzzle def')
            self.journal.protected_steps += 1
            self.generating: bool = True

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
                        region_eliminate(self,cell,digit,f'c{cell}')
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
                    proof_gen = fill(self,cell,digit)
                case 'have':
                    # the rest of the line is the goal
                    goal = cmd.removeprefix('have').strip()
                    if goal == "":
                        raise CommandError("expected 'have [goal]'")
                    proof_gen = have(self,'h',goal)
                case 'cell_cases':
                    if len(params) != 1:
                        raise CommandError("expected 'cell_cases cell'")
                    try:
                        cell = int(params[0])
                    except ValueError:
                        raise CommandError('cell must be an integer')
                    proof_gen = cell_cases(self,cell)
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
                    proof_gen = rfl(self)
                case 'exact':
                    if len(params) != 1:
                        raise CommandError("expected 'exact hypothesis'")
                    proof_gen = exact(self,params[0])
                case 'naked_single':
                    if len(params) != 1:
                        raise CommandError("expected 'naked_single cell")
                    try:
                        cell = int(params[0])
                    except ValueError:
                        raise CommandError('cell must be an integer')
                    proof_gen = cast(ProofGenerator,naked_single(self,cell))
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
