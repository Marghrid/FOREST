from abc import ABC, abstractmethod
from itertools import chain
from typing import cast, List, Any

from forest.spec import Type, Production, EnumProduction, ParamProduction, \
    FunctionProduction


class Node(ABC):
    '''Generic and abstract AST Node'''

    @abstractmethod
    def __init__(self, prod: Production):
        self._prod = prod

    @property
    def production(self) -> Production:
        return self._prod

    @property
    def type(self) -> Type:
        return self._prod.lhs

    @abstractmethod
    def is_leaf(self) -> bool:
        raise NotImplementedError

    @abstractmethod
    def is_enum(self) -> bool:
        raise NotImplementedError

    @abstractmethod
    def is_param(self) -> bool:
        raise NotImplementedError

    @abstractmethod
    def is_apply(self) -> bool:
        raise NotImplementedError

    @property
    @abstractmethod
    def children(self) -> List['Node']:
        raise NotImplementedError

    def depth(self):
        if not self.has_children():
            return 1
        else:
            # Compute the depth of each subtree
            children_depths = map(lambda ch: ch.depth(), self.children)

            # Use the larger one
            return 1 + max(children_depths)

    def has_children(self):
        return self.children is not None and len(self.children) > 0

    def get_subtree(self):
        """ Return as an ordered list all the descendant nodes """
        if not self.is_apply():
            assert not self.has_children()
            return []
        if not self.has_children():
            return [self]
        else:
            return [self] + list(chain(*map(lambda c: c.get_subtree(), self.children)))

    def get_leaves(self):
        """ Return a list of all leaves, ordered from left to right """
        if not self.has_children():
            return []
        else:
            if len(self.children) == 1 and self.children[0].is_apply() and self.children[0].name == "re":
                return [self] + list(chain.from_iterable(map(lambda c: c.get_leaves(), self.children)))
            if not self.children[0].is_apply():
                return [self] + list(chain.from_iterable(map(lambda c: c.get_leaves(), self.children)))
            if len(self.children) > 1 and not self.children[1].is_apply():
                return [self] + list(chain.from_iterable(map(lambda c: c.get_leaves(), self.children)))
            else:
                return list(chain(*map(lambda c: c.get_leaves(), self.children)))


class LeafNode(Node):
    '''Generic and abstract class for AST nodes that have no children'''

    @abstractmethod
    def __init__(self, prod: Production):
        super().__init__(prod)
        if prod.is_function():
            raise ValueError(
                'Cannot construct an AST leaf node from a FunctionProduction')

    def is_leaf(self) -> bool:
        return True

    def is_apply(self) -> bool:
        return False


class AtomNode(LeafNode):
    """Leaf AST node that holds string data"""

    def __init__(self, prod: Production):
        if not prod.is_enum():
            raise ValueError(
                'Cannot construct an AST atom node from a non-enum production')
        super().__init__(prod)
        self.data = self.get_data()

    def get_data(self) -> Any:
        prod = cast(EnumProduction, self._prod)
        return prod.rhs[0]

    @property
    def children(self) -> List[Node]:
        return []

    def is_enum(self) -> bool:
        return True

    def is_param(self) -> bool:
        return False

    def deep_eq(self, other) -> bool:
        '''
        Test whether this node is the same with ``other``. This function performs deep comparison rather than just comparing the object identity.
        '''
        if isinstance(other, AtomNode):
            return self.type == other.type and self.data == other.data
        return False

    def deep_hash(self) -> int:
        '''
        This function performs deep hash rather than just hashing the object identity.
        '''
        return hash((self.type, str(self.data)))

    def __repr__(self) -> str:
        return 'AtomNode({})'.format(self.data)

    def __str__(self) -> str:
        return '{}'.format(self.data)


class ParamNode(LeafNode):
    '''Leaf AST node that holds a param'''

    def __init__(self, prod: Production):
        if not prod.is_param():
            raise ValueError(
                'Cannot construct an AST param node from a non-param production')
        super().__init__(prod)

    @property
    def index(self) -> int:
        prod = cast(ParamProduction, self._prod)
        return prod.rhs[0]

    @property
    def children(self) -> List[Node]:
        return []

    def is_enum(self) -> bool:
        return False

    def is_param(self) -> bool:
        return True

    def deep_eq(self, other) -> bool:
        '''
        Test whether this node is the same with ``other``. This function performs deep comparison rather than just comparing the object identity.
        '''
        if isinstance(other, ParamNode):
            return self.index == other.index
        return False

    def deep_hash(self) -> int:
        '''
        This function performs deep hash rather than just hashing the object identity.
        '''
        return hash(self.index)

    def __repr__(self) -> str:
        return 'ParamNode({})'.format(self.index)

    def __str__(self) -> str:
        return '@param{}'.format(self.index)


class ApplyNode(Node):
    """Internal AST node that represent function application"""

    def __init__(self, prod: Production, args: List[Node]):
        super().__init__(prod)
        if not prod.is_function():
            raise ValueError(
                'Cannot construct an AST internal node from a non-function production')
        for index, (decl_ty, node) in enumerate(zip(prod.rhs, args)):
            actual_ty = node.type
            if decl_ty != actual_ty:
                msg = f'Argument {index} type mismatch on {prod}: expected {decl_ty} but found {actual_ty}'
                raise ValueError(msg)
        self._args = args

    @property
    def name(self) -> str:
        prod = cast(FunctionProduction, self._prod)
        return prod.name

    @property
    def args(self) -> List[Node]:
        return self._args

    @property
    def children(self) -> List[Node]:
        return self._args

    def is_leaf(self) -> bool:
        return False

    def is_enum(self) -> bool:
        return False

    def is_param(self) -> bool:
        return False

    def is_apply(self) -> bool:
        return True

    def deep_eq(self, other) -> bool:
        '''
        Test whether this node is the same with ``other``. This function performs deep comparison rather than just comparing the object identity.
        '''
        if isinstance(other, ApplyNode):
            return self.name == other.name and \
                   len(self.args) == len(other.args) and \
                   all(x.deep_eq(y)
                       for x, y in zip(self.args, other.args))
        return False

    def deep_hash(self) -> int:
        '''
        This function performs deep hash rather than just hashing the object identity.
        '''
        return hash((self.name, tuple(map(lambda x: x.deep_hash(), self.args))))

    def __repr__(self) -> str:
        return f'ApplyNode({self.name}, {self._args})'

    def __str__(self) -> str:
        return f'{self.name}({", ".join(map(str, self._args))})'
