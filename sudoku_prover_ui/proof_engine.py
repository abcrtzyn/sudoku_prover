#pyright: standard

import re
from typing import Any, Dict, Generator, List, NoReturn, Optional, Tuple
from pantograph import Server
from pantograph.expr import Site, Tactic, TacticHave, TacticExpr, TacticLet, TacticMode, GoalState

from sudoku_prover_ui.sudoku_state import SudokuState

from pathlib import Path

# __file__ is .../sudoku_prover_ui/proof_engine.py
# .parent is .../sudoku_prover_ui/
# .parent.parent is the repo root
REPO_ROOT = Path(__file__).resolve().parent.parent


SYMBOLS = [1,2,3,4]
MAX_CELLS = 16
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
    def __init__(self, num_cells: int, puzzle: str):
        self.server = Server(project_path=REPO_ROOT,imports=[ # type: ignore
            'Mathlib.Tactic.IntervalCases',
            'SudokuProverLogic.Basic',
            'SudokuProverLogic.Symbols4',
            'SudokuProverLogic.Tactics'
        ],timeout=60)
        grid: List[int | None] = [None for _ in range(num_cells)]
        eliminations: Dict[int,Dict[int,Tuple[str,Any]]] = {}

        # give the puzzle to Lean
        self.server.load_definitions(puzzle)

        # start the proof
        proof_state = self.server.goal_start("∀ (S: Set (Nat → Symbols4)) (_ : ∀ f, f ∈ S ↔ TestPuzzle f), ∃! (g: Nat -> Symbols4), g ∈ S")
        proof_state = self.server.goal_tactic(proof_state, 
"""intro S H
have k: IsSound S [] := by intro c d h; cases h""")
        self.symbols = SYMBOLS
        self.current = SudokuState(proof_state,grid,eliminations)

        self.undo_stack: List[SudokuState] = []
        self.history: List[str] = []
        self.active_gen: Generator[str, str, None] = self.controller()
        
        # process the puzzle input

        # process given digits
        for k,v in givens.items():
            # add the given to the k structure
            self.tactic(
f"""replace k := add_fact k {k} {v} (by
intro f hf
replace H := (H f).mp hf
apply H.given{k})""")
            
            # create elimination proofs for each
            self.current.grid[k] = v
            self.region_eliminate(k,v)


    
    def tactic(self, tactic: Tactic):
        """helper that handles the state variables
        updates the proof state and returns it"""
        new_state = self.server.goal_tactic(self.current.proof_state, tactic)
        # can handle errors here
        # before updating state
        self.current.proof_state = new_state

        return self.current.proof_state

    def region_eliminate(self, cell: int,digit: int):
        """eliminates all of digit from every cell in every region that cell is a part of"""
        for r in regions_search[cell]:
            for i in regions[r]:
                if i == cell:
                    continue
                # we have a choice to override a current elimination rule, or keep the first one
                # there are pros and cons to either, but that is for future me to decide.
                # this code OVERRIDES existing elemination rules
                if i not in self.current.eliminations:
                    self.current.eliminations[i] = dict()
                self.current.eliminations[i][digit] = ('digit_in_region', (cell,digit,r))


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


    def have(self, goal: str) -> Generator[str,str,None]:
        """generates a have goal in Lean, can be anything at this point, there will be rules later..."""
        goals_count = self.current.count_goals()
        self.tactic(TacticHave(goal,'h'))
        # check if it is a top level have, that needs the forall f in S removed
        if self.current.proof_state.goals[0].target.startswith('∀ f ∈ S'):
            print('did the thing')
            self.tactic("""intro f hf; replace H := (H f).mp hf""")
        # solve the goal using a command
        cmd = yield goal
        yield from self.handle_input(cmd)

        if self.current.count_goals() > goals_count:
            print('the have goal was not finished')
            exit(6)


    def fill(self, cell: int, digit: int) -> Generator[str,str,None]:
        """special case to fill a cell with a digit, creates the goal and after is proved, adds it to the datastructures and creates eliminations"""
        yield from self.have(f'∀ f ∈ S, f {cell} = {digit}')
        self.tactic(f"""replace k := add_fact k {cell} {digit} h; clear h""")
        
        self.current.grid[cell] = digit
        self.region_eliminate(cell,digit)

    def cell_cases(self, cell) -> Generator[str,str,None]:
        goals_count = self.current.count_goals()
        self.tactic(f'cases h: f {cell}')
        # we know the order of these cases, it's exactly the order of the symbols
        for digit in SYMBOLS:
            if cell in self.current.eliminations and digit in self.current.eliminations[cell]:
                self.generate_elimination_proof(cell,digit,'h')
            # TODO we also need to check for accepting cases, not yet
            else:
                cmd = yield f'cell_cases {digit}'
                yield from self.handle_input(cmd)
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

    def support_cases(self, hypothesis: str, digit: int | None) -> Generator[str,str,None]:
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
                cmd = yield f'support_cases {cell}'
                yield from self.handle_input(cmd)
        
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
        if region in regions:
            # check if it is the correct size for surjective logic
            if len(regions[region]) != len(SYMBOLS):
                print("can't do surjective logic on a unique set that isn't the same size as symbols")
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
            if not (0 <= cell < MAX_CELLS):
                raise CommandError(f'cell {cell} out of range')
            if digit not in SYMBOLS:
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
            if not (0 <= cell < MAX_CELLS):
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
            if digit not in SYMBOLS:
                raise CommandError(f'digit {digit} invalid')
            yield from self.support_cases_manual(digit, region)
        elif name == 'rfl':
            if len(params) != 0:
                raise CommandError("expected 'rfl' with no arguments")
            self.tactic('rfl')
        elif name == 'exact':
            if len(params) != 1:
                raise CommandError("expected 'exact hypothesis'")
            self.tactic(f'exact {params[0]}')
        else:
            raise CommandError(f'unknown command {name}')
        # elif args[0] == 'naked' and 2 <= len(args):
        #     cell = int(args[1])
        #     # naked takes a cell number, anything after is not used
        #     # the command succeeds if the cell only has one candidate
        #     if digit := naked_single(cell):
        #         self.change_cell(cell,digit)
        #         region_eliminate(cell,digit)
        # elif args[0] == 'hidden' and 2 <= len(args):
        #     digit = int(args[1])
        #     region = args[2]
        #     # hidden takes a digit and region, anything after is not used
        #     # the command succeeds if the region only has one cell without digit eliminated
        #     if cell := hidden_single(self.grid,digit,region):
        #         self.change_cell(cell, digit)
        #         region_eliminate(cell,digit)

    def controller(self) -> Generator[str,str,None]:
        """main logic loop for cli"""
        while True:
            cmd = yield ''
            try:
                yield from self.handle_input(cmd)
            except CommandError as e:
                print(f'[!] {e}')




puzzle = """
structure TestPuzzle (solution: Nat -> Symbols4) where
  row1: UniqueSet solution { 0, 1, 2, 3}
  row2: UniqueSet solution { 4, 5, 6, 7}
  row3: UniqueSet solution { 8, 9,10,11}
  row4: UniqueSet solution {12,13,14,15}
  col1: UniqueSet solution { 0, 4, 8,12}
  col2: UniqueSet solution { 1, 5, 9,13}
  col3: UniqueSet solution { 2, 6,10,14}
  col4: UniqueSet solution { 3, 7,11,15}
  box1: UniqueSet solution { 0, 1, 4, 5}
  box2: UniqueSet solution { 2, 3, 6, 7}
  box3: UniqueSet solution { 8, 9,12,13}
  box4: UniqueSet solution {10,11,14,15}
  given2: solution 2 = 4
  given4: solution 4 = 4
  given6: solution 6 = 3
  given9: solution 9 = 4
  given11: solution 11 = 3
  given13: solution 13 = 1
  outside_grid: ∀ x, x ≥ 16 -> solution x = Symbols4.one -- just need something to call default
"""

regions: Dict[str,List[int]] = {
    'row1': [ 0, 1, 2, 3],
    'row2': [ 4, 5, 6, 7],
    'row3': [ 8, 9,10,11],
    'row4': [12,13,14,15],
    'col1': [ 0, 4, 8,12],
    'col2': [ 1, 5, 9,13],
    'col3': [ 2, 6,10,14],
    'col4': [ 3, 7,11,15],
    'box1': [ 0, 1, 4, 5],
    'box2': [ 2, 3, 6, 7],
    'box3': [ 8, 9,12,13],
    'box4': [10,11,14,15],
}
givens = {
    2: 4,
    4: 4,
    6: 3,
    9: 4,
    11: 3,
    13: 1,
}

regions_search: List[List[str]] = []

def generate_search():
    for _ in range(81):
        regions_search.append([])
    for r in regions:
        for c in regions[r]:
            regions_search[c].append(r)

generate_search()









# # this is where the proof begins
# control = controller()
# prompt = next(control)

# while True:
#     print(current_state.goals[0])
#     cmd = input(f'{prompt}{' ' if prompt else ''}> ').strip()
#     prompt = control.send(cmd)

