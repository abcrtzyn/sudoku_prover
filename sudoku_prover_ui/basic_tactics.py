

from sudoku_prover_ui.proof_engine import ProofEngine, ProofGenerator


def region_eliminate(engine: ProofEngine, cell: int,digit: int,proof_name:str):
    """eliminates all of digit from every cell in every region that cell is a part of"""
    for name, constraint in engine.puzzle.pythonized_constraints.items():
        if constraint[0] != 'UniqueSet':
            continue
        if cell in constraint[1]:
            for i in constraint[1]:
                if i == cell:
                    continue        
                # we have a choice to override a current elimination rule, or keep the first one
                # there are pros and cons to either, but that is for future me to decide.
                # this code OVERRIDES existing elemination rules
                if i not in engine.prepared_elimination_changes:
                    engine.prepared_elimination_changes[i] = dict()
                engine.prepared_elimination_changes[i][digit] = ('digit_in_region', (cell,name,proof_name))



def generate_elimination_proof(engine: ProofEngine,cell: int, digit: int, hypothesis: str):
    """Given the current cell and digit and hypothesis name to eliminate
    eliminates this contradictory case"""
    
    if engine.current.grid[cell] is not None:
        proof = f'exact digit_in_cell {hypothesis} (c{cell} P)'
        engine.tactic(f'exfalso; {proof}')
    elif cell in engine.current.eliminations and digit in engine.current.eliminations[cell]:
        elim = engine.current.eliminations[cell][digit]
        if elim[0] == 'digit_in_region':
            proof = f'exact digit_in_region {hypothesis} P.{elim[1][1]} ({elim[1][2]} P)'
        else:
            print('unknown elimination reason',elim[0])
            exit(4)
        engine.tactic(f'exfalso; {proof}')
    else:
        print(f'no elimination present for {cell} {digit}')
        exit(5)

@ProofEngine.command_flow
def have(engine: ProofEngine, name: str, goal: str):
    """generates a have goal in Lean, can be anything at this point, there will be rules later..."""

    yield lambda: None

    def run() -> ProofGenerator:
        # if it is a top level goal, need to start a new lemma, otherwise do a have statement
        if engine.proof_level == 0:
            engine.tactic(f"lemma {name} {{f: Nat -> {engine.puzzle.symbols}}} (P: Puzzle f): {goal} := by")
        else:
            engine.tactic(f"have {name}: {goal} := by")
        with engine.indent():
            yield from engine.do_subproof(goal)
            
        if engine.proof_level == 0:
            # add a newline for top level goals.
            engine.tactic('')

    return run
    
@ProofEngine.command_flow
def fill(engine: ProofEngine, cell: int, digit: int):
    """special case to fill a cell with a digit, creates the goal and after is proved, adds it to the datastructures and creates eliminations"""

    def validate():
        if not (0 <= cell < engine.puzzle.cell_count):
            raise ValueError(f'cell {cell} out of range')
        if digit not in engine.puzzle.symbols_python:
            raise ValueError(f'digit {digit} invalid')

    yield validate

    def run() -> ProofGenerator:
        # set up what changes will occur after the subproof
        engine.prepared_grid_changes[cell] = digit
        region_eliminate(engine,cell,digit,f'c{cell}')

        yield from have(engine,f'c{cell}', f'f {cell} = {digit}')
        
    return run


@ProofEngine.command_flow
def cell_cases(engine: ProofEngine, cell: int):

    def validate():
        if not (0 <= cell < engine.puzzle.cell_count):
            raise ValueError(f'cell {cell} out of range')

    yield validate

    def run() -> ProofGenerator:
        engine.tactic(f'cases h: f {cell}')
        
        with engine.indent():
            # we know the order of these cases, it's exactly the order of the symbols
            for digit in engine.puzzle.symbols_python:
                engine.place_dot()
                if cell in engine.current.eliminations and digit in engine.current.eliminations[cell]:
                    generate_elimination_proof(engine,cell,digit,'h')
                    # TODO we also need to check for accepting cases, not yet
                else:
                    yield from engine.do_subproof(f'cell_cases {digit}')
    
    return run
        

# #     def support_cases(engine, hypothesis: str, digit: int | None, commands: Dict[int,Generator[str,str,None]] | None = None) -> Generator[str,str,None]:
# #         """Does support_cases or locked_support_cases on the hypothesis and digit
# #         the hypothesis is must be of the form SupportSet {...} n or LockedSet {...} {...}
# #         This function will detect which one is needed. If the hypothesis is a locked set, a digit must be given"""
# #         for var in engine.current.proof_state.goals[0].variables:
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
# #         engine.tactic(f"""{'locked_support_cases' if region_is_locked else 'support_cases'} h {digit}""")
# #         with engine.indent():
# #             for cell in cell_set:
# #                 engine.place_dot()
# #                 if (engine.current.grid[cell] is not None) or (cell in engine.current.eliminations and digit in engine.current.eliminations[cell]):
# #                     engine.generate_elimination_proof(cell,digit,'h')
# #                 # TODO we also need to check for accepting cases, not yet
# #                 else:
# #                     yield from engine._execute_dict_or_prompt(commands,cell,f'support_cases {cell}')
        
    
# #     def support_cases_manual(engine, digit: int, region: str) -> Generator[str,str,None]:
# #         # couple things we have to do in order to call support cases
# #         # one, create the hypothesis to run cases on, which has many cases
# #         # is there a hypothesis by that name in the context?
# #         qualified_region_name = None
# #         if region in engine.puzzle.pythonized_constraints:
# #             # check if it is the correct size for surjective logic
# #             if engine.puzzle.pythonized_constraints[region][0] != 'UniqueSet':
# #                 raise ValueError(f'Can not do support_cases on region {region}')
# #             cells = engine.puzzle.pythonized_constraints[region][1]

# #             if len(cells) != len(engine.puzzle.symbols_python):
# #                 raise ValueError("can't do surjective logic on a unique set that isn't the same size as symbols")
# #             qualified_region_name = f'(region_full_locked_set H.{region})'
# #         else:
# #             for var in engine.current.proof_state.goals[0].variables:
# #                 if var.name == region:
# #                     break
# #             else:
# #                 print('could not find a region by that name in the context')
# #             # TODO for now, assume that it starts with forall f in S
# #             qualified_region_name = f'{region} f hf'
# #         engine.tactic(f'let h := {qualified_region_name}')

# #         yield from engine.support_cases('h',digit)

@ProofEngine.command_flow
def rfl(engine: ProofEngine):
    yield lambda: None

    def run():
        engine.tactic('rfl')
        return

    return run

@ProofEngine.command_flow
def exact(engine: ProofEngine,hypothesis: str):
    yield lambda: None
    
    def run():
        engine.tactic(f'exact {hypothesis}')
        return

    return run

@ProofEngine.command_flow
def naked_single(engine: ProofEngine,cell: int):

    def validate():
        if not (0 <= cell < engine.puzzle.cell_count):
            raise ValueError('naked_single cell must be an index from 0 to cell_count')
        
    yield validate

    # first find the digit to fill (check that all digits but one are eliminated)
    if cell not in engine.current.eliminations:
        # definetely not able to eliminate the candidates
        raise ValueError(f'cell {cell} has more than one candidate, can not do naked_single')
    elims = engine.current.eliminations[cell]
        
    not_eliminated = None
    for digit in engine.puzzle.symbols_python:
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
        engine.no_commit_flag += 1
        # naked single macro. fills the cell with the digit by doing cases on that cell
        # yield from engine.fill(cell,digit,engine.cell_cases(cell,{digit: engine.rfl()}))
        # for right now, this function has to has to handle the genartors itengine
        gen = fill(engine,cell,digit)
        _ = next(gen)
        _ = gen.send(cell_cases(engine,cell))
        try:
            _ = gen.send(rfl(engine))
        except StopIteration:
            pass
        
        engine.no_commit_flag -= 1

        return
    
    return run

