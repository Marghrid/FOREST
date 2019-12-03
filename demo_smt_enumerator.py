#!/usr/bin/env python

import tyrell.spec as S
from tyrell.interpreter import PostOrderInterpreter
from tyrell.enumerator import SmtEnumerator
from tyrell.decider import Example, ExampleConstraintDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger

logger = get_logger('tyrell')

class ToyInterpreter(PostOrderInterpreter):
    def eval_Regex(self, v):
        return int(v)

    def eval_Bool(self, v):
        return int(v)

    def eval_Kleene(self, node, args):
        return args[0]

    def eval_Eval(self, node, args):
        return args[0]


def main():
    logger.info('Parsing Spec...')
    spec = S.parse_file('example/regex.tyrell')
    logger.info('Parsing succeeded')

    logger.info('Building synthesizer...')
    synthesizer = Synthesizer(
        enumerator=SmtEnumerator(spec, depth=3, loc=2),
        decider=ExampleConstraintDecider(
            spec=spec,
            interpreter=ToyInterpreter(),
            examples=[
                # we want to synthesize the program (x-y)*y (depth=3, loc=2)
                # which is also equivalent to x*y-y*y (depth=3, loc=3)
                Example(input=[3], output=3),
            ]
        )
    )
    logger.info('Synthesizing programs...')

    prog = synthesizer.synthesize()
    if prog is not None:
        logger.info('Solution found: {}'.format(prog))
    else:
        logger.info('Solution not found!')


if __name__ == '__main__':
    logger.setLevel('DEBUG')
    main()
