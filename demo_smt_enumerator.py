#!/usr/bin/env python

import tyrell.spec as S
from tyrell.interpreter import PostOrderInterpreter
from tyrell.enumerator import SmtEnumerator
from tyrell.decider import Example, ExampleConstraintDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger

import re

logger = get_logger('tyrell')

class ToyInterpreter(PostOrderInterpreter):
	def eval_Regex(self, v):
		return int(v)

	def eval_Bool(self, v):
		return int(v)

	def eval_MkRegex(self, node, args):
		return args[0]

	def eval_Kleene(self, node, args):
		'''
		Returns the string args[1] without the first match with regex (args[0])*
		'''
		regex = fr'(({args[0]})*)'                    # to feed the python function
		matchings = re.match(regex, args[1]).groups() # all matchings
		if len(matchings) == 0: return args[1]        # there is no matching
		print('kleene', regex, args[1], '->', args[1].replace(matchings[0], '', 1))
		return args[1].replace(matchings[0], '', 1)


	def eval_Concat(self, node, args):
		'''
		Returns the string args[2] without the first match with
		regex (args[0])(args[1])
		'''
		regex = fr'(({args[0]})({args[1]}))'          # to feed the python function
		matchings = re.match(regex, args[1]).groups() # all matchings
		if len(matchings) == 0: return args[1]        # there is no matching
		print('concat', regex, args[1], '->', args[1].replace(matchings[0], '', 1))
		return args[1].replace(matchings[0], '', 1)

	def eval_Match(self, node, args):
		return len(args[0]) == 0


def main():
	logger.info('Parsing Spec...')
	spec = S.parse_file('example/regex.tyrell')
	logger.info('Parsing succeeded')

	logger.info('Building synthesizer...')
	synthesizer = Synthesizer(
		enumerator=SmtEnumerator(spec, depth=6, loc=6),
		decider=ExampleConstraintDecider(
			spec=spec,
			interpreter=ToyInterpreter(),
			examples=[
				Example(input=['is'], output=True),
				#Example(input='', output=True),
				Example(input=['si'], output=False),
				Example(input=['t'], output=False),
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
