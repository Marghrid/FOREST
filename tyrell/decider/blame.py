from typing import NamedTuple

from ..dsl import Node
from ..spec import Production

Blame = NamedTuple('Blame', [('node', Node), ('production', Production)])

# The default printer for Blame is too verbose. We use a simplified version here.


def print_blame(blame: Blame) -> str:
    return 'Blame(node={}, production={})'.format(blame.node, blame.production.id)


Blame.__str__ = print_blame  # type: ignore
Blame.__repr__ = print_blame  # type: ignore
