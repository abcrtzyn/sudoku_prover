

from dataclasses import dataclass
from typing import Callable, Concatenate, Dict, List, TYPE_CHECKING

from sudoku_prover_app.core.argument_parser import IMPLEMENTED_TYPES
from sudoku_prover_app.core.types import ProofGenerator

if TYPE_CHECKING:
    from sudoku_prover_app.core.proof_engine import ProofEngine



@dataclass

class CommandEntry:
    func: Callable[Concatenate['ProofEngine',...],ProofGenerator]
    arg_type: List[str]

class CommandRegistry:
    def __init__(self):
        self.commands: Dict[str, CommandEntry] = {}
        
    def register(self, name: str, arg_types: List[str]):
        """Decorator to register a tactic with expected arguments"""
        # check that all the arg types can be parsed by the parser
        for t in arg_types:
            if t not in IMPLEMENTED_TYPES:
                raise NotImplementedError(f'argument parser says argument of type {t} is not implemented')

        def decorator(func: Callable[Concatenate['ProofEngine',...],ProofGenerator]):
            if not getattr(func, '_is_command_flow', False):
                raise TypeError('Tactic must have decoration @command_flow before being registered (means put @registry.register(), then @command_flow, then def func)')

            self.commands[name] = CommandEntry(func, arg_types)
            return func
        
        return decorator


registry = CommandRegistry()


