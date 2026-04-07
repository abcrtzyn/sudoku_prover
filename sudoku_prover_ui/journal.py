

from copy import deepcopy
from dataclasses import dataclass, field
from typing import Any, Dict, Generator, List, Tuple

@dataclass
class Delta:
    """A class to represent a proof section. Each delta will be a sub-proof (list of commands) or a single user command"""
    user_commands: List[str]
    lean_code: str
    # for now, only additions to both these fields are allowed
    # I currently see no reason to
    grid_changes: Dict[int,int] # these are the additions to the grid
    elimination_changes: Dict[int,Dict[int,Tuple[str,Any]]] # these are additions to eliminations

@dataclass
class State:
    grid: List[int | None]
    commands_list: List[str] = field(default_factory=list) # pyright: ignore[reportUnknownVariableType]
    lean_file: str = ''
    eliminations: Dict[int,Dict[int,Tuple[str,Any]]] = field(default_factory=dict) # pyright: ignore[reportUnknownVariableType]
    # proof_state is the lean context. proof_state is None if unknown, [] if no goals, has items when there are goals
    proof_state: List[str] | None = field(default=None) # pyright: ignore[reportUnknownVariableType]

    def copy(self) -> "State":
        """Create a copy of this state"""
        return State(self.grid.copy(),self.commands_list.copy(),self.lean_file,deepcopy(self.eliminations),self.proof_state)

    def add_journal(self, jrnl: "Journal"):
        for delta in jrnl:
            self.add_delta(delta)
        self.proof_state = None
    

    def add_delta(self, delta: Delta, proof_state: List[str] | None = None):
        self.commands_list += delta.user_commands
        self.lean_file += delta.lean_code
        for cell, digit in delta.grid_changes.items():
            self.grid[cell] = digit
        for cell, d in delta.elimination_changes.items():
            if cell not in self.eliminations:
                self.eliminations[cell] = dict()
            for digit, info in d.items():
                self.eliminations[cell][digit] = info
        self.proof_state = proof_state

    def count_goals(self):
        if self.proof_state is None:
            raise Exception('proof state is unknown at count_goals')
        return len(self.proof_state)

class Journal:
    _history: List[Delta] = []
    protected_steps = 0

    def __init__(self, history: List[Delta] | None):
        self._history = history or []

    def __iter__(self):
        return iter(self._history)
    
    def __len__(self):
        return len(self._history)

    def add(self,delta: Delta):
        self._history.append(delta)
    
    def pop(self):
        if len(self._history) <= self.protected_steps:
            raise ValueError('Could not pop from journal, steps are protected or list is empty')
        self._history.pop()

    def pop_subproof(self, index: int):
        steps = self._history[index:]
        self._history = self._history[:index]
        return Journal(steps)


    def commands(self) -> Generator[str, None, None]:
        for delta in self._history:
            yield from delta.user_commands
    
    def lean_code_file(self) -> str:
        code_str = ''
        for delta in self._history:
            code_str += delta.lean_code
            
        return code_str
