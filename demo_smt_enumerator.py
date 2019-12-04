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
		# args[0] is a char, arg[1] is a string.
		ret_string = args[1]
		while(len(ret_string) > 0 and ret_string[-1] == args[0]):
			ret_string = ret_string[:-1]
		return ret_string

	def eval_Match(self, node, args):
		return len(args[0]) == 0


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
				Example(input='iii', output=True),
				Example(input='i', output=True),
				#Example(input='', output=True),
				Example(input='s', output=False),
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
