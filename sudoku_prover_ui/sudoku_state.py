
from copy import deepcopy
from typing import Any, Dict, List, Tuple

class SudokuState:
    """State of the sudoku proof, stores the Lean proof state and other data structures used by the program"""
    
    def __init__(self, proof_state: List[str], grid: List[int | None], eliminations: Dict[int,Dict[int,Tuple[str,Any]]]):
        self.proof_state: List[str] = proof_state
        self.grid: List[int | None] = grid
        self.eliminations: Dict[int,Dict[int,Tuple[str,Any]]] = eliminations
    
    def snapshot(self):
        """creates a copy of the state for undo"""
        return SudokuState(self.proof_state,self.grid.copy(),deepcopy(self.eliminations))

    def count_goals(self):
        return len(self.proof_state)
