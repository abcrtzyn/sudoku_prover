import re
from typing import Any, Dict, List, Optional, Tuple
from pantograph import Server
from pantograph.expr import Site, TacticHave, TacticExpr, TacticLet, TacticMode, GoalState

SYMBOLS = [1,2,3,4]


word_to_number = {
    'one': 1,
    'two': 2,
    'three': 3,
    'four': 4,
    'five': 5,

}



server = Server(project_path=".",imports=[
    'Mathlib.Tactic.IntervalCases',
    'SudokuLean.Basic',
    'SudokuLean.Symbols4',
    'SudokuLean.Tactics'
],timeout=60)

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


grid: List[int | None] = [None for _ in range(16)]
eliminations: Dict[int,Dict[int,Tuple[str,Any]]] = {}


def region_eliminate(cell: int,digit: int):
    """eliminates all of digit from every cell in every region that cell is a part of"""
    for r in regions_search[cell]:
        for i in regions[r]:
            if i == cell:
                continue
            # we have a choice to override a current elimination rule, or keep the first one
            # there are pros and cons to either, but that is for future me to decide.
            # this code OVERRIDES existing elemination rules
            if i not in eliminations:
                eliminations[i] = dict()
            eliminations[i][digit] = ('digit_in_region', (cell,digit,r))


server.is_automatic()
current_state: GoalState


def generate_elimination_proof(cell: int, digit: int, hypothesis: str):
    """Given the current cell and digit and hypothesis name to eliminate
    eliminates this contradictory case"""
    global current_state
    goals_count = len(current_state.goals)
    if grid[cell] is not None:
        proof = f'exact digit_in_cell {hypothesis} ((get_d k {cell} {grid[cell]}) f hf)'
        current_state = server.goal_tactic(current_state, f'exfalso; {proof}')
    elif cell in eliminations and digit in eliminations[cell]:
        elim = eliminations[cell][digit]
        if elim[0] == 'digit_in_region':
            proof = f'exact digit_in_region {hypothesis} H.{elim[1][2]} ((get_d k {elim[1][0]} {elim[1][1]}) f hf)'
        else:
            print('unknown elimination reason',elim[0])
            exit(4)

        current_state = server.goal_tactic(current_state, f'exfalso; {proof}')
    else:
        print(f'no elimination present for {cell} {digit}')
        exit(5)
    if len(current_state.goals) != goals_count - 1:
        # not the correct number of goals
        if len(current_state.goals) < goals_count - 1:
            print(current_state.goals)
            print('generate_elimination_proof managed to solve more cases than it was supposed to. Did you dormant a goal?')
            exit(6)
        else:
            print(current_state.goals)
            print('generate_elimination_proof did not prove all the cases')
            exit(7)
    
    

def generate_elimination_proof_manual(hypothesis: str):
    """Finds out the values of cell and digit from the hypothesis and eliminates the case"""
    global current_state
    for var in current_state.goals[0].variables:
        if var.name == hypothesis:
            break
    else:
        print(f'could not find a hypothesis {hypothesis} in the context')
        exit(2)
    mat = re.match('f (\\d+) = (Symbols\\d+\\.(\\w+)|(\\d+))',var.t)
    if mat is None:
        print(f'{var.t} did not match the re')
        exit(3)
    cell = int(mat.group(1))
    if mat.group(4) is not None:
        digit = int(mat.group(4))
    else:
        digit = word_to_number[mat.group(3)]
    
    generate_elimination_proof(cell,digit,hypothesis)


def have(goal: str):
    """generates a have goal in Lean, can be anything at this point, there will be rules later..."""
    global current_state
    goals_count = len(current_state.goals)
    current_state = server.goal_tactic(current_state,TacticHave(goal,'h'))
    # check if it is a top level have, that needs the forall f in S removed
    if current_state.goals[0].target.startswith('∀ f ∈ S'):
        print('did the thing')
        current_state = server.goal_tactic(current_state,"""intro f hf; replace H := (H f).mp hf""")
    # solve the goal using a command
    cmd = yield goal
    yield from handle_input(cmd)

    if len(current_state.goals) > goals_count:
        print('the have goal was not finished')
        exit(6)


def fill(cell: int, digit: int):
    """special case to fill a cell with a digit, creates the goal and after is proved, adds it to the datastructures and creates eliminations"""
    global current_state
    yield from have(f'∀ f ∈ S, f {cell} = {digit}')
    current_state = server.goal_tactic(current_state,f"""replace k := add_fact k {cell} {digit} h; clear h""")
    grid[cell] = digit
    region_eliminate(cell,digit)

def cell_cases(cell):
    global current_state
    goals_count = len(current_state.goals)
    current_state = server.goal_tactic(current_state,f'cases h: f {cell}')
    # we know the order of these cases, it's exactly the order of the symbols
    for digit in SYMBOLS:
        if cell in eliminations and digit in eliminations[cell]:
            generate_elimination_proof(cell,digit,'h')
        # TODO we also need to check for accepting cases, not yet
        else:
            cmd = yield f'cell_cases {digit}'
            yield from handle_input(cmd)
    if len(current_state.goals) != goals_count - 1:
        # not the correct number of goals
        if len(current_state.goals) < goals_count - 1:
            print(current_state.goals)
            print('cell_cases managed to solve more cases than it was supposed to. Did you dormant a goal?')
            exit(6)
        else:
            print(current_state.goals)
            print('cell_cases did not prove all the cases')
            exit(7)

def support_cases(hypothesis: str, digit: int | None):
    """Does support_cases or locked_support_cases on the hypothesis and digit
    the hypothesis is must be of the form SupportSet {...} n or LockedSet {...} {...}
    This function will detect which one is needed. If the hypothesis is a locked set, a digit must be given"""
    global current_state
    goals_count = len(current_state.goals)

    for var in current_state.goals[0].variables:
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

    current_state = server.goal_tactic(current_state,
f"""{'locked_support_cases' if region_is_locked else 'support_cases'} h {digit}
""")
    print(cell_set)
    for cell in cell_set:
        if (grid[cell] is not None) or (cell in eliminations and digit in eliminations[cell]):
            generate_elimination_proof(cell,digit,'h')
        # TODO we also need to check for accepting cases, not yet
        else:
            cmd = yield f'support_cases {cell}'
            yield from handle_input(cmd)
    
    if len(current_state.goals) != goals_count - 1:
        # not the correct number of goals
        if len(current_state.goals) < goals_count - 1:
            print(current_state.goals)
            print('support_cases managed to solve more cases than it was supposed to. Did you dormant a goal?')
            exit(6)
        else:
            print(current_state.goals)
            print('support_cases did not prove all the cases')
            exit(7)
    
def support_cases_manual(digit: int, region: str):
    global current_state
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
        for var in current_state.goals[0].variables:
            if var.name == region:
                break
        else:
            print('could not find a region by that name in the context')
        # TODO for now, assume that it starts with forall f in S
        qualified_region_name = f'{region} f hf'
    
    current_state = server.goal_tactic(current_state,f'let h := {qualified_region_name}')

    yield from support_cases('h',digit)


def handle_input(cmd: str):
    global current_state
    args = cmd.split()
    if args[0] == 'exit':
        exit(0)
    elif args[0] == 'fill':
        cell = int(args[1])
        digit = int(args[2])
        yield from fill(cell,digit)
    elif args[0] == 'have':
        goal = cmd.removeprefix('have').strip()
        yield from have(goal)
    elif args[0] == 'cell_cases':
        cell = int(args[1])
        yield from cell_cases(cell)
    elif args[0] == 'support_cases':
        region = args[1]
        digit = int(args[2])
        yield from support_cases_manual(digit, region)
    elif args[0] == 'rfl':
        current_state = server.goal_tactic(current_state,'rfl')
    elif args[0] == 'exact':
        current_state = server.goal_tactic(current_state, f'exact {args[1]}')
    elif args[0] == 'elim':
        hypothesis = args[1]
        generate_elimination_proof_manual(hypothesis)
    else:
        print('unknown command')
        exit(1)
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

def controller():
    """main logic loop for cli"""
    while True:
        cmd = yield ''
        try:
            yield from handle_input(cmd)
        except Exception as e:
            print('bad input')
            print(e)


# give the puzzle to Lean
server.load_definitions(puzzle)

# start the proof
state0 = server.goal_start("∀ (S: Set (Nat → Symbols4)) (_ : ∀ f, f ∈ S ↔ TestPuzzle f), ∃! (g: Nat -> Symbols4), g ∈ S")

state1 = server.goal_tactic(state0, 
"""intro S H
have k: IsSound S [] := by intro c d h; cases h""")

# step 0
# process given digits
current_state = state1
for k,v in givens.items():
    # add the given to the k structure
    current_state = server.goal_tactic(current_state, f"""replace k := add_fact k {k} {v} (by
    intro f hf
    replace H := (H f).mp hf
    apply H.given{k})""")
    # create elimination proofs for each
    grid[k] = v
    region_eliminate(k,v)

# this is where the proof begins
control = controller()
prompt = next(control)

while True:
    print(current_state.goals[0])
    cmd = input(f'{prompt}{' ' if prompt else ''}> ').strip()
    prompt = control.send(cmd)



print(current_state)
print(current_state.goals)


# state2 = server.goal_tactic(state1,TacticHave("∀ f ∈ S, f 5 = 2",'c5'))


