#!/usr/bin/env python

import re, sys
import tyrell.spec as S
from tyrell.interpreter import PostOrderInterpreter
from tyrell.enumerator import RandomEnumerator
from tyrell.decider import Example, ExampleDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger

logger = get_logger('tyrell')

def execute(interpreter, prog, args):
    return interpreter.eval(prog, args)


def test_all(interpreter, prog, inputs, outputs):
    return all(
        execute(interpreter, prog, inputs[x]) == outputs[x]
        for x in range(0, len(inputs))
    )


def main(seed=None):
    logger.info('Parsing Spec...')
    spec = S.parse_file('DSLs/regex2.tyrell')
    logger.info('Parsing succeeded')

    logger.info('Building synthesizer...')
    synthesizer = Synthesizer(
        enumerator=RandomEnumerator( spec, max_depth=6, seed=seed),
        decider=ExampleDecider(
            interpreter=ToyInterpreter(),
            examples=[
                Example(input=['ist193985'], output=True),
                Example(input=['ist425891'], output=True),
                Example(input=['ist187769'], output=True),
                Example(input=['ist194149'], output=True),
                Example(input=['ist181361'], output=True),
                Example(input=['ist426036'], output=True),
                Example(input=['ist178742'], output=True),
                Example(input=['ist191063'], output=True),
                Example(input=['ist181338'], output=True),
                Example(input=['ist178022'], output=True),
                Example(input=['ist425904'], output=True),
                Example(input=['ist426008'], output=True),

                Example(input=['193985'],    output=False),
                Example(input=['ost425891'], output=False),
                Example(input=['ist187'],    output=False),
                Example(input=['426036'],    output=False),
                Example(input=['st181361'],  output=False),
                Example(input=['is426036'],  output=False),
                Example(input=['iat178742'], output=False),
                Example(input=['ist19106'],  output=False)
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
    seed = None
    if len(sys.argv) > 1:
        try:
            seed = int(sys.argv[1])
        except ValueError:
            pass
    main(seed)
