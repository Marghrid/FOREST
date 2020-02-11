#!/usr/bin/env python

import tyrell.spec as S
from tyrell.interpreter import PostOrderInterpreter
from tyrell.enumerator import SmtEnumerator
from tyrell.decider import Example, ValidationDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger
import re, sys

logger = get_logger('tyrell')

def my_equal_output(prog, input, desired_output):
    interpreter = RegexInterpreter()
    try:
        output = interpreter.eval(prog,input)
        return output == desired_output
    except:
        return False


def main():
    logger.info('Parsing Spec...')
    spec = S.parse_file('DSLs/regex2.tyrell')
    logger.info('Parsing succeeded')

    logger.info('Building synthesizer...')
    synthesizer = Synthesizer(
        enumerator=SmtEnumerator(spec, depth=6, loc=14),
        decider=ValidationDecider(
            spec=spec,
            interpreter=RegexInterpreter(),
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

                Example(input=['193985'], output=False),
                Example(input=['ost425891'], output=False),
                Example(input=['ist187'], output=False),
                Example(input=['426036'], output=False),
                Example(input=['st181361'], output=False),
                Example(input=['is426036'], output=False),
                Example(input=['iat178742'], output=False),
                Example(input=['ist19106'], output=False)
            ],
            equal_output=my_equal_output
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
