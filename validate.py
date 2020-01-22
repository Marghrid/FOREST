#!/usr/bin/env python

import tyrell.spec as S
from tyrell.interpreter import PostOrderInterpreter
from tyrell.enumerator import SmtEnumerator
from tyrell.decider import Example, ExampleConstraintDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger
import re, sys

logger = get_logger('tyrell')


class ToyInterpreter(PostOrderInterpreter):
    def eval_Regex(self, v):
        return int(v)

    def eval_Bool(self, v):
        return int(v)

    def eval_re(self, node, args):
        return fr'{args[0]}'

    def eval_kleene(self, node, args):
        if len(args[0]) == 1: return fr'{args[0]}*'
        return fr'({args[0]})*'

    def eval_concat(self, node, args):
        return fr'{args[0]}{args[1]}'

    def eval_union(self, node, args):
        if len(args[0]) == 1:
            h0 = fr'{args[0]}'
        else:
            h0 = fr'({args[0]})'
        if len(args[1]) == 1:
            h1 = fr'{args[1]}'
        else:
            h1 = fr'({args[1]})'
        return h0 + '|' + h1

    def eval_match(self, node, args):
        match = re.fullmatch(args[0], args[1])
        # print('match', args[0], args[1], match is not None)
        if match is not None: print(args[0], 'accepts', args[1], file=sys.stderr)
        return match is not None


def main():
    logger.info('Parsing Spec...')
    spec = S.parse_file('example/regex2.tyrell')
    logger.info('Parsing succeeded')

    logger.info('Building synthesizer...')
    synthesizer = Synthesizer(
        enumerator=SmtEnumerator(spec, depth=6, loc=14),
        decider=ExampleConstraintDecider(
            spec=spec,
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

                Example(input=['193985'], output=False),
                Example(input=['ost425891'], output=False),
                Example(input=['ist187'], output=False),
                Example(input=['426036'], output=False),
                Example(input=['st181361'], output=False),
                Example(input=['is426036'], output=False),
                Example(input=['iat178742'], output=False),
                Example(input=['ist19106'], output=False)
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
