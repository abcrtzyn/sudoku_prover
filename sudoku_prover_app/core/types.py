

from typing import Callable, Generator

class CommandError(Exception):
    pass


ProofGenerator = Generator[str | CommandError,'ProofGenerator',None]
ValidateFunc = Callable[[],None]
RunFunc = Callable[[],ProofGenerator|None]
CommandTemplate = Generator[ValidateFunc,None,RunFunc]
