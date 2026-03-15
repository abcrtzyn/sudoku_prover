import re
from typing import Any, Dict, List, Optional, Tuple
from pantograph import Server
from pantograph.expr import Site, TacticHave, TacticExpr, TacticMode, GoalState

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
], timeout=60)

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


# manual eliminations, automatic eliminations for naked single or hidden single
# will occur at the time
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

# def naked_single(cell: int):
#     """returns the digit in a cell because it is the only candidate left
#     this function is not very protective, it currently only checks 1-9 and first checks for exactly 8 digit eliminations"""
#     elims = eliminations[cell]
#     if len(elims.keys()) != 8:
#         return None
#     # good length
#     for d in range(1,10):
#         if d not in elims.keys():
#             return d
#     raise ValueError(f'naked cell can\'t handle whatever happened. naked_cell({cell})')
    
# def hidden_single(grid: List[Optional[int]], digit: int, region: str):
#     """returns the only cell where a digit appears in a region
#     this function is not very protective, it currently assumes that all regions have the surjective property"""
#     current_find = None
#     for cell in regions[region]:
#         if grid[cell] is not None:
#             continue
#         if cell in eliminations:
#             if digit in eliminations[cell]:
#                 continue
#         # else case for both, digit not eliminated
#         if current_find is not None:
#             # more than one cell is possible
#             return None
#         # else, set it
#         current_find = cell
#     # only one cell is not eliminated
#     return current_find

current_state: GoalState

def have(goal: str):
    global current_state
    goals_count = len(current_state.goals)
    current_state = server.goal_tactic(current_state,TacticHave(goal,'h'))
    if current_state.goals[0].target.startswith('∀ f ∈ S'):
        print('did the thing')
        current_state = server.goal_tactic(current_state,"""intro f hf; replace H := (H f).mp hf""")
    cmd = yield
    yield from handle_input(cmd)
    if len(current_state.goals) > goals_count:
        print('the have goal was not finished')
        exit(6)


def fill(cell: int, digit: int):
    global current_state
    yield from have(f'∀ f ∈ S, f {cell} = {digit}')
    current_state = server.goal_tactic(current_state,f"""replace k := add_fact k {cell} {digit} h; clear h""")
    region_eliminate(cell,digit)

def cell_cases(cell):
    global current_state
    goals_count = len(current_state.goals)
    current_state = server.goal_tactic(current_state,f'cases h: f {cell}')
    # keep asking for proofs until all cases are closed
    while len(current_state.goals) >= goals_count:
        cmd = yield
        yield from handle_input(cmd)
    
def generate_elimination_proof(hypothesis: str):
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
    if cell in eliminations and digit in eliminations[cell]:
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
    elif args[0] == 'rfl':
        current_state = server.goal_tactic(current_state,'rfl')
    elif args[0] == 'elim':
        hypothesis = args[1]
        generate_elimination_proof(hypothesis)
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
    region_eliminate(k,v)

# this is where the proof begins

while True:
    print(current_state.goals[0])
    cmd = input('> ').strip()
    gen = handle_input(cmd)
    try:
        next(gen)
        while True:
            print(current_state.goals[0])
            cmd = input('> ').strip()
            gen.send(cmd)
    except StopIteration:
        pass



print(current_state)
print(current_state.goals)


# state2 = server.goal_tactic(state1,TacticHave("∀ f ∈ S, f 5 = 2",'c5'))


