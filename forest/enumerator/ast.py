from itertools import chain


class AST:
    def __init__(self, tree_id=0):
        self.head = None
        self.id = tree_id
        self.nodes = []


class ASTNode:
    def __init__(self, nb=None, depth=None, children=None, tree_id=0):
        self.id = nb
        self.tree_id = tree_id
        self.depth = depth
        self.children = children
        self.production = None

    def has_children(self):
        return self.children is not None and len(self.children) > 0

    def get_subtree(self):
        """ Return as an ordered list all the descendant nodes """
        if not self.has_children():
            return [self]
        else:
            assert len(self.children) == 2
            return [self] + list(chain(*map(lambda c: c.get_subtree(), self.children)))
