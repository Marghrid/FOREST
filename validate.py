#!/usr/bin/env python

import tyrell.spec as S
from tyrell.enumerator import SmtEnumerator
from tyrell.decider import Example, ExampleConstraintDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger
from validation_interpreter import ValidationInterpreter

logger = get_logger('tyrell')


def my_equal_output(prog, input, desired_output):
    interpreter = ValidationInterpreter()
    try:
        output = interpreter.eval(prog,input)
        return output == desired_output
    except:
        return False

def main():
    logger.info('Parsing Spec...')
    spec = S.parse_file('example/validationDSL.tyrell')
    logger.info('Parsing succeeded')
    logger.info('Building synthesizer...')
    for dep in range(1, 6):
        try:
            enumerator = SmtEnumerator(spec, depth=dep, loc=4)
        except RuntimeError as e:
            print(e)
            continue
        synthesizer = Synthesizer(
            enumerator=enumerator,
            decider=ExampleConstraintDecider(
                spec=spec,
                interpreter=ValidationInterpreter(),
                examples=[
                    Example(input=['1'], output=True),
                    Example(input=['2'], output=True),
                    Example(input=['3'], output=True),
                    Example(input=['4'], output=True),
                    Example(input=['5'], output=True),

                    Example(input=['0'], output=False),
                    Example(input=['six'], output=False),
                ],
                equal_output=my_equal_output
            )
        )
        logger.info(f'Synthesizing programs of depth {dep}')

        prog = synthesizer.synthesize()
        if prog is not None:
            logger.info('Solution found: {}'.format(prog))
            logger.info(f'depth: {dep}, loc: {l}')
            return
    logger.info('Solution not found!')


if __name__ == '__main__':
    logger.setLevel('DEBUG')
    main()
