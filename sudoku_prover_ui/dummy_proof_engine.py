
## used to test ui stuff because Lean takes so long to load
# in main.py
#     import this file
#     change ProofEngine to DummyProofEngine
#     test all the ui stuff you want with fast start up 


from sudoku_prover_ui.journal import State
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

class DummyGoalState:
    def __init__(self):
        self.goals = []



class DummyProofEngine:
    def __init__(self, puzzle: Puzzle):
        self.puzzle = puzzle
        del puzzle
        self.server = None # Server(project_path=REPO_ROOT,imports=[ # type: ignore
        #     'Mathlib.Tactic.IntervalCases',
        #     'SudokuProverLogic.Basic',
        #     f'SudokuProverLogic.{self.puzzle.symbols}',
        #     'SudokuProverLogic.Tactics'
        # ],timeout=60)

        # give the puzzle to Lean
        # self.server.load_definitions(self.puzzle.generate_lean_structure()) # pyright: ignore[reportUnknownMemberType]
        self.terminal_prompt = ''
        # start the proof
        # proof_state = self.server.goal_start(f"∀ (S: Set (Nat → {self.puzzle.symbols})) (_ : ∀ f, f ∈ S ↔ Puzzle f), ∃! (g: Nat -> {self.puzzle.symbols}), g ∈ S") # pyright: ignore[reportUnknownMemberType]
        # proof_state = self.server.goal_tactic(proof_state,  # pyright: ignore[reportUnknownMemberType]
# """intro S H
# have k: IsSound S [] := by intro c d h; cases h""")
        self.current = State([None]*self.puzzle.cell_count,)
        
        # process the puzzle constraints
        for _, constraint in self.puzzle.pythonized_constraints.items():
            match constraint[0]:
                case 'Given':
                    cell = constraint[1][0]
                    digit = constraint[1][1]
                    
                    # create elimination proofs for each
                    self.current.grid[cell] = digit
                case _:
                    pass

    
    def command(self,cmd:str):
        print('I am dummy')
        # self.terminal_prompt = self._active_gen.send(cmd)
        return ''
