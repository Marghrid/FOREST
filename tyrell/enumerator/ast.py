class AST:
    def __init__(self, id = 0):
        self.head = None
        self.id = id
        self.nodes = []


class ASTNode:
    def __init__(self, nb=None, depth=None, children=None, tree_id = 0):
        self.id = nb
        self.tree_id = tree_id
        self.depth = depth
        self.children = children
        self.production = None

    def has_children(self):
        return self.children is not None and len(self.children) > 0