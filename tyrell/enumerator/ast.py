class AST:
    def __init__(self):
        self.head = None


class ASTNode:
    def __init__(self, nb=None, depth=None, children=None):
        self.id = nb
        self.depth = depth
        self.children = children
        self.production = None