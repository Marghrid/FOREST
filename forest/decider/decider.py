from abc import ABC, abstractmethod
from typing import Any

from .result import Result
from ..dsl import Node
from ..visitor import InterpreterError


class Decider(ABC):

    @abstractmethod
    def __init__(self):
        self._interpreter = None

    @abstractmethod
    def analyze(self, ast: Node) -> Result:
        """
        The main API of this class. It is expected to analyze the given AST and check
        if it is valid. If not, optionally returns why, which is used to update the
        enumerator.
        """
        raise NotImplementedError

    def analyze_interpreter_error(self, error: InterpreterError) -> Any:
        """
        Take an visitor error and return a data structure that can be used to update
        the enumerator.
        """
        return None

    def interpreter(self):
        return self._interpreter
