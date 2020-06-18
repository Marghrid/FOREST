from typing import List, Any

from .context import Context
from .error import InterpreterError, GeneralError
from .interpreter import Interpreter
from ..dsl import Node, AtomNode, ParamNode, ApplyNode
from ..generic_visitor import GenericVisitor


class NodeVisitor(GenericVisitor):

    def __init__(self, interp, inputs):
        super().__init__()
        self._interp = interp
        self.inputs = inputs
        self.context = Context()

    def visit_with_context(self, node: Node):
        self.context.observe(node)
        res = self.visit(node)
        self.context.finish(node)
        return res

    def visit_atom_node(self, atom_node: AtomNode):
        method_name = self._eval_method_name(atom_node.type.name)
        method = getattr(self._interp, method_name, lambda x: x)
        return method(atom_node.data)

    def visit_param_node(self, param_node: ParamNode):
        param_index = param_node.index
        if param_index >= len(self.inputs):
            msg = 'Input parameter access({}) out of bound({})'.format(
                param_index, len(self.inputs))
            raise GeneralError(msg)
        return self.inputs[param_index]

    def visit_apply_node(self, apply_node: ApplyNode):
        in_values = [self.visit_with_context(
            x) for x in apply_node.args]
        self.context.pop()
        method_name = self._eval_method_name(apply_node.name)
        method = getattr(self._interp, method_name,
                         self._method_not_found)
        return method(apply_node, in_values)

    def _method_not_found(self, apply_node: ApplyNode, arg_values: List[Any]):
        msg = 'Cannot find required eval method: "{}"'.format(
            self._eval_method_name(apply_node.name))
        raise NotImplementedError(msg)

    @staticmethod
    def _eval_method_name(name):
        return 'eval_' + name


class PostOrderInterpreter(Interpreter):

    def eval(self, program: Node, inputs=None) -> Any:
        """
        Interpret the Given AST in post-order. Assumes the existence of `eval_XXX` method
        where `XXX` is the name of a function defined in the DSL.
        """
        node_visitor = NodeVisitor(self, inputs)
        try:
            return node_visitor.visit_with_context(program)
        except InterpreterError as e:
            e.context = node_visitor.context
            raise e from None
