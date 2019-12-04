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
		return fr'{args[0]}'

	def eval_Kleene(self, node, args):
		if len(args[0]) == 1: return fr'{args[0]}*'
		return fr'({args[0]})*'

	def eval_Concat(self, node, args):
		if len(args[0]) == 1: h0 = fr'{args[0]}'
		else: h0 = fr'({args[0]})'
		if len(args[1]) == 1: h1 = fr'{args[1]}'
		else: h1 = fr'({args[1]})'
		return h0 + h1

	def eval_Union(self, node, args):
		if len(args[0]) == 1: h0 = fr'{args[0]}'
		else: h0 = fr'({args[0]})'
		if len(args[1]) == 1: h1 = fr'{args[1]}'
		else: h1 = fr'({args[1]})'
		return h0 + '|' + h1

	def eval_Match(self, node, args):
		match = re.fullmatch(args[0], args[1])
		# print('match', args[0], args[1], match is not None)
		if match is not None: print(args[0], 'accepts', args[1])
		return match is not None


def main():
	logger.info('Parsing Spec...')
	spec = S.parse_file('example/regex2.tyrell')
	logger.info('Parsing succeeded')

	logger.info('Building synthesizer...')
	synthesizer = Synthesizer(
		enumerator=SmtEnumerator(spec, depth=7, loc=7),
		decider=ExampleConstraintDecider(
			spec=spec,
			interpreter=ToyInterpreter(),
			examples=[
				Example(input=['Daniel'], output=True),
				Example(input=['Danieel'], output=True),
				Example(input=['Danieeeel'], output=True),
				Example(input=['Danieeeeeeel'], output=True),
				Example(input=['Danilol'], output=False),
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
