
import re
from typing import Any, Dict, Generator, List, Tuple
from pantograph import Server # pyright: ignore[reportMissingTypeStubs]
from pantograph.expr import Tactic, TacticHave # pyright: ignore[reportMissingTypeStubs]

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
    def __init__(self, puzzle: Puzzle):
        self.puzzle = puzzle
        del puzzle
        self.server = Server(project_path=REPO_ROOT,imports=[ # type: ignore
            'Mathlib.Tactic.IntervalCases',
            'SudokuProverLogic.Basic',
            f'SudokuProverLogic.{self.puzzle.symbols}',
            'SudokuProverLogic.Tactics'
        ],timeout=60)
        grid: List[int | None] = [None for _ in range(self.puzzle.cell_count)]
        eliminations: Dict[int,Dict[int,Tuple[str,Any]]] = {}

        # give the puzzle to Lean
        self.server.load_definitions(self.puzzle.generate_lean_structure()) # pyright: ignore[reportUnknownMemberType]

        # start the proof
        proof_state = self.server.goal_start(f"∀ (S: Set (Nat → {self.puzzle.symbols})) (_ : ∀ f, f ∈ S ↔ Puzzle f), ∃! (g: Nat -> {self.puzzle.symbols}), g ∈ S") # pyright: ignore[reportUnknownMemberType]
        proof_state = self.server.goal_tactic(proof_state,  # pyright: ignore[reportUnknownMemberType]
"""intro S H
have k: IsSound S [] := by intro c d h; cases h""")
        self.current = SudokuState(proof_state,grid,eliminations)

        self.undo_stack: List[SudokuState] = []
        self.history: List[str] = []
        self._active_gen: Generator[str, str, None] = self.controller()
        self.terminal_prompt = next(self._active_gen)
        
        # process the puzzle constraints
        for name, constraint in self.puzzle.constraints_python.items():
            match constraint[0]:
                case 'Given':
                    cell = constraint[1][0]
                    digit = constraint[1][1]
                    self.tactic(
f"""replace k := add_fact k {cell} {digit} (by
intro f hf
replace H := (H f).mp hf
apply H.{name})""")
            
                    # create elimination proofs for each
                    self.current.grid[cell] = digit
                    self.region_eliminate(cell,digit)
                case 'UniqueSet':
                    pass
                case _:
                    raise NotImplementedError(f'constraint of type {constraint[0]} has no implementation for initialization')



    
    def tactic(self, tactic: Tactic):
        """helper that handles the state variables
        updates the proof state and returns it"""
        new_state = self.server.goal_tactic(self.current.proof_state, tactic) # pyright: ignore[reportUnknownMemberType]
        # can handle errors here
        # before updating state
        self.current.proof_state = new_state

        return self.current.proof_state

    def _execute_or_prompt(self, command: Generator[str, str, None] | None, prompt: str) -> Generator[str, str, None]:
        """if a command is given, run the command, else, get one from the interface and run it"""
        if command is not None:
            yield from command
        else:
            cmd = yield prompt
            yield from self.handle_input(cmd)
    
    def _execute_dict_or_prompt[K](self, commands: Dict[K,Generator[str,str,None]] | None, key: K, prompt: str) -> Generator[str, str, None]:
        """if a command is given, run the command, else, get one from the interface and run it"""
        if commands is not None and key in commands:
            yield from commands[key]
        else:
            cmd = yield prompt
            yield from self.handle_input(cmd)

    def region_eliminate(self, cell: int,digit: int):
        """eliminates all of digit from every cell in every region that cell is a part of"""
        for name, constraint in self.puzzle.constraints_python.items():
            if constraint[0] != 'UniqueSet':
                continue
            if cell in constraint[1]:
                for i in constraint[1]:
                    if i == cell:
                        continue        
                    # we have a choice to override a current elimination rule, or keep the first one
                    # there are pros and cons to either, but that is for future me to decide.
                    # this code OVERRIDES existing elemination rules
                    if i not in self.current.eliminations:
                        self.current.eliminations[i] = dict()
                    self.current.eliminations[i][digit] = ('digit_in_region', (cell,digit,name))


    def generate_elimination_proof(self,cell: int, digit: int, hypothesis: str):
        """Given the current cell and digit and hypothesis name to eliminate
        eliminates this contradictory case"""
        
        goals_count = self.current.count_goals()
        if self.current.grid[cell] is not None:
            proof = f'exact digit_in_cell {hypothesis} ((get_d k {cell} {self.current.grid[cell]}) f hf)'
            self.tactic(f'exfalso; {proof}')
        elif cell in self.current.eliminations and digit in self.current.eliminations[cell]:
            elim = self.current.eliminations[cell][digit]
            if elim[0] == 'digit_in_region':
                proof = f'exact digit_in_region {hypothesis} H.{elim[1][2]} ((get_d k {elim[1][0]} {elim[1][1]}) f hf)'
            else:
                print('unknown elimination reason',elim[0])
                exit(4)
            self.tactic(f'exfalso; {proof}')
        else:
            print(f'no elimination present for {cell} {digit}')
            exit(5)
        if self.current.count_goals() != goals_count - 1:
            # not the correct number of goals
            if  self.current.count_goals() < goals_count - 1:
                print(self.current.proof_state.goals)
                print('generate_elimination_proof managed to solve more cases than it was supposed to. Did you dormant a goal?')
                exit(6)
            else:
                print(self.current.proof_state.goals)
                print('generate_elimination_proof did not prove all the cases')
                exit(7)


    def have(self, goal: str, command: Generator[str,str,None] | None = None) -> Generator[str,str,None]:
        """generates a have goal in Lean, can be anything at this point, there will be rules later..."""
        goals_count = self.current.count_goals()
        self.tactic(TacticHave(goal,'h'))
        # check if it is a top level have, that needs the forall f in S removed
        if self.current.proof_state.goals[0].target.startswith('∀ f ∈ S'):
            print('did the thing')
            self.tactic("""intro f hf; replace H := (H f).mp hf""")
        # solve the goal using a command
        yield from self._execute_or_prompt(command,goal)

        if self.current.count_goals() > goals_count:
            print('the have goal was not finished')
            exit(6)


    def fill(self, cell: int, digit: int, command: Generator[str,str,None] | None = None) -> Generator[str,str,None]:
        """special case to fill a cell with a digit, creates the goal and after is proved, adds it to the datastructures and creates eliminations"""
        yield from self.have(f'∀ f ∈ S, f {cell} = {digit}',command)
        self.tactic(f"""replace k := add_fact k {cell} {digit} h; clear h""")
        
        self.current.grid[cell] = digit
        self.region_eliminate(cell,digit)

    def cell_cases(self, cell: int, commands: Dict[int,Generator[str,str,None]] | None = None) -> Generator[str,str,None]:
        goals_count = self.current.count_goals()
        self.tactic(f'cases h: f {cell}')
        # we know the order of these cases, it's exactly the order of the symbols
        for digit in self.puzzle.symbols_python:
            if cell in self.current.eliminations and digit in self.current.eliminations[cell]:
                self.generate_elimination_proof(cell,digit,'h')
                # TODO we also need to check for accepting cases, not yet
            else:
                yield from self._execute_dict_or_prompt(commands,digit,f'cell_cases {digit}')
            
        if self.current.count_goals() != goals_count - 1:
            # not the correct number of goals
            if self.current.count_goals() < goals_count - 1:
                print(self.current.proof_state.goals)
                print('cell_cases managed to solve more cases than it was supposed to. Did you dormant a goal?')
                exit(6)
            else:
                print(self.current.proof_state.goals)
                print('cell_cases did not prove all the cases')
                exit(7)

    def support_cases(self, hypothesis: str, digit: int | None, commands: Dict[int,Generator[str,str,None]] | None = None) -> Generator[str,str,None]:
        """Does support_cases or locked_support_cases on the hypothesis and digit
        the hypothesis is must be of the form SupportSet {...} n or LockedSet {...} {...}
        This function will detect which one is needed. If the hypothesis is a locked set, a digit must be given"""
        goals_count = self.current.count_goals()

        for var in self.current.proof_state.goals[0].variables:
            if var.name == hypothesis:
                break
        else:
            print(f'could not find a hypothesis {hypothesis} in the context')
            exit(2)
        pattern = r'(?P<type>Locked|Support)Set f \{(?P<data>\d+(?:,\s*\d+)*)\} (?P<digit>\S|.+)'
        mat = re.match(pattern, var.t)
        if mat is None:
            print(f'{var.t} did not match the re')
            exit(7)
        region_is_locked = mat.group('type') == 'Locked'
        cell_set = [int(x.strip()) for x in mat.group('data').split(',')]
        # if it is a support set, get the digit from the hypothesis
        if not region_is_locked:
            digit = int(mat.group('digit'))
        
        if digit is None:
            print('no digit provided for locked set')
            exit(8)
        self.tactic(f"""{'locked_support_cases' if region_is_locked else 'support_cases'} h {digit}""")
        
        for cell in cell_set:
            if (self.current.grid[cell] is not None) or (cell in self.current.eliminations and digit in self.current.eliminations[cell]):
                self.generate_elimination_proof(cell,digit,'h')
            # TODO we also need to check for accepting cases, not yet
            else:
                yield from self._execute_dict_or_prompt(commands,cell,f'support_cases {cell}')
        
        if self.current.count_goals() != goals_count - 1:
            # not the correct number of goals
            if self.current.count_goals() < goals_count - 1:
                print(self.current.proof_state.goals)
                print('support_cases managed to solve more cases than it was supposed to. Did you dormant a goal?')
                exit(6)
            else:
                print(self.current.proof_state.goals)
                print('support_cases did not prove all the cases')
                exit(7)
        
    def support_cases_manual(self, digit: int, region: str) -> Generator[str,str,None]:
        # couple things we have to do in order to call support cases
        # one, create the hypothesis to run cases on, which has many cases
        # is there a hypothesis by that name in the context?
        qualified_region_name = None
        if region in self.puzzle.constraints_python:
            # check if it is the correct size for surjective logic
            if self.puzzle.constraints_python[region][0] != 'UniqueSet':
                raise CommandError(f'Can not do support_cases on region {region}')
            cells = self.puzzle.constraints_python[region][1]

            if len(cells) != len(self.puzzle.symbols_python):
                raise CommandError("can't do surjective logic on a unique set that isn't the same size as symbols")
            qualified_region_name = f'(region_full_locked_set H.{region})'
        else:
            for var in self.current.proof_state.goals[0].variables:
                if var.name == region:
                    break
            else:
                print('could not find a region by that name in the context')
            # TODO for now, assume that it starts with forall f in S
            qualified_region_name = f'{region} f hf'
        self.tactic(f'let h := {qualified_region_name}')

        yield from self.support_cases('h',digit)

    def rfl(self) -> Generator[str,str,None]:
        self.tactic('rfl')
        return
        yield
    
    def exact(self,hypothesis: str) -> Generator[str,str,None]:
        self.tactic(f'exact {hypothesis}')
        return
        yield

    def naked_single(self,cell: int) -> Generator[str,str,None]:
        # first find the digit to fill (check that all digits but one are eliminated)
        if cell not in self.current.eliminations:
            # definetely not able to eliminate the candidates
            raise CommandError(f'cell {cell} has more than one candidate, can not do naked_single')
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
                raise CommandError(f'cell {cell} has more than one candidate, can not do naked_single')
        
        if not_eliminated is None:
            # this cell has no candidates, solve using cell_cases instead
            raise CommandError(f'cell {cell} has no candidates, this should be solved by cell_cases')
        digit = not_eliminated
        
        # naked single macro. fills the cell with the digit by doing cases on that cell
        yield from self.fill(cell,digit,self.cell_cases(cell,{digit: self.rfl()}))

    def finish(self):
        """Where all the digits are known, this function finishes out the proof.
        This finishes out the proof by 
        - creating the function g, 
        - proving it satisfies all constraints (which could need some proof help, but most of it should be automatic)
        - showing that it is the only function using all the proofs of each digit that were created in the solving process"""

        # going to be using it a lot, so local variable
        grid = self.current.grid


        if any([x is None for x in grid]):
            # not all digits are known.
            raise CommandError('Not all digits are solved, can not finish proof')
        

        # create the function g and use it
        # using the digits proved to create the function
        self.tactic(
f"""let digits: Array Symbols4 := #{grid}
-- for use later, say how long it is
have len: digits.size = {len(grid)} := by decide
-- define the function g and use it
let g : Nat → Symbols4 := fun x => digits[x]? |>.getD 1
use g
constructor -- splits into testing constraints and uniqueness
simp only
apply (H g).mpr
""")
        # next is to prove that obeys the constraints of the puzzle
        # this is done by splitting up the structure
        # at this point it is all hard coded to the specific puzzle
        # later there will be functions to prove UniqueSet constraints, theromemeters, etc.
        self.tactic(
"""constructor
-- outside the grid
intro n hn
unfold g
conv => enter [1, 1]; apply Array.getElem?_eq_none (by {rw [len]; assumption})
simp
iterate 12 apply injOn_by_card; decide --UniqueSet
iterate 6 decide -- givens
"""
        )   
        # uniqueness start here
        self.tactic(
f"""intro h hh
replace H := (H h).mp hh
ext x
by_cases xin: x < {len(grid)}
interval_cases x
"""
        )
        # now to get the proof for each cell
        for cell,digit in enumerate(grid):
            self.tactic(f'exact (get_d k {cell} {digit}) h hh')
        # and handle the outside the grid normalization
        self.tactic(
f"""rw [H.outside_grid]
unfold g
simp at xin
conv => enter [2,1]; apply Array.getElem?_eq_none (by {{rw [len]; assumption}})
simp
push_neg at xin
apply xin
"""
        )


    def handle_input(self, cmd: str) -> Generator[str,str,None]:
        if cmd == '':
            raise CommandError("No command given")
        args = cmd.split()
        name = args[0]
        params = args[1:]
        if name == 'exit':
            # ignores all arguments
            exit(0)
        elif name == 'fill':
            if len(params) != 2:
                raise CommandError("expected 'fill cell digit'")
            try:
                cell = int(params[0])
                digit = int(params[1])
            except ValueError:
                raise CommandError('digit and cell must be integers')
            if not (0 <= cell < self.puzzle.cell_count):
                raise CommandError(f'cell {cell} out of range')
            if digit not in self.puzzle.symbols_python:
                raise CommandError(f'digit {digit} invalid')
            yield from self.fill(cell,digit)
        elif name == 'have':
            # the rest of the line is the goal
            goal = cmd.removeprefix('have').strip()
            if goal == "":
                raise CommandError("expected 'have [goal]'")
            yield from self.have(goal)
        elif name == 'cell_cases':
            if len(params) != 1:
                raise CommandError("expected 'cell_cases cell'")
            try:
                cell = int(params[0])
            except ValueError:
                raise CommandError('cell must be an integer')
            if not (0 <= cell < self.puzzle.cell_count):
                raise CommandError(f'cell {cell} out of range')
            yield from self.cell_cases(cell)
        elif name == 'support_cases':
            if len(params) != 2:
                raise CommandError("expected 'support_cases region digit'")
            region = params[0]
            try: 
                digit = int(params[1])
            except ValueError:
                raise CommandError('digit must be an integer')
            if digit not in self.puzzle.symbols_python:
                raise CommandError(f'digit {digit} invalid')
            yield from self.support_cases_manual(digit, region)
        elif name == 'rfl':
            if len(params) != 0:
                raise CommandError("expected 'rfl' with no arguments")
            yield from self.rfl()
        elif name == 'exact':
            if len(params) != 1:
                raise CommandError("expected 'exact hypothesis'")
            yield from self.exact(params[0])
        elif name == 'naked_single':
            if len(params) != 1:
                raise CommandError("expected 'naked_single cell")
            try:
                cell = int(params[0])
            except ValueError:
                raise CommandError('cell must be an integer')
            if not (0 <= cell < self.puzzle.cell_count):
                raise CommandError(f'cell {cell} out of range')
            yield from self.naked_single(cell)
        elif name == 'finish':
            if len(params) != 0:
                raise CommandError('finish takes no args')
            self.finish()
        else:
            raise CommandError(f'unknown command {name}')
        

    def controller(self) -> Generator[str,str,None]:
        """main logic loop for cli"""
        while True:
            cmd = yield ''
            try:
                yield from self.handle_input(cmd)
            except CommandError as e:
                print(f'[!] {e}')
    
    def command(self,cmd:str):
        self.terminal_prompt = self._active_gen.send(cmd)
        return self.terminal_prompt
