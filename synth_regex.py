#!/usr/bin/env python3
import argparse
import random
from signal import signal, SIGINT, SIGTERM
from typing import List, Tuple

from termcolor import colored

from forest.dsl.dsl_builder import DSLBuilder
from forest.logger import get_logger
from forest.parse_examples import parse_file, parse_resnax
from forest.spec import TyrellSpec
from forest.synthesizer import MultiTreeSynthesizer, KTreeSynthesizer, LinesSynthesizer, \
    SketchSynthesizer
from forest.utils import conditions_to_str
from forest.visitor import RegexInterpreter

logger = get_logger('forest')

synthesizer = None


def sig_handler(received_signal, frame):
    print('\nSIGINT or SIGTERM detected. Exiting gracefully.')
    if synthesizer is not None:
        print('Printing the last valid program found.')
        synthesizer.die = True


def main():
    signal(SIGINT, sig_handler)
    signal(SIGTERM, sig_handler)
    examples_file, encoding, self_interact, resnax, no_pruning, max_valid, max_invalid, \
    sketching_mode = read_cmd_args()

    if resnax:
        valid, invalid, ground_truth = parse_resnax(examples_file)
        condition_invalid = []
    else:
        valid, invalid, condition_invalid, ground_truth = parse_file(examples_file)

    random.seed("regex")
    if 0 < max_valid < len(valid):
        valid = random.sample(valid, max_valid)
    if 0 < max_invalid < len(invalid):
        invalid = random.sample(invalid, max_invalid)

    show(valid, invalid, condition_invalid, ground_truth)
    if sketching_mode != 'none':
        sketch_synthesize(valid, invalid, condition_invalid, sketching_mode, ground_truth,
                          self_interact)
    elif encoding == 'multitree':
        multitree_synthesize(valid, invalid, condition_invalid, ground_truth,
                             self_interact, no_pruning)
    elif encoding == "dynamic":
        dynamic_synthesize(valid, invalid, condition_invalid, ground_truth, self_interact,
                           no_pruning)
    elif encoding == 'ktree':
        ktree_synthesize(valid, invalid, condition_invalid, ground_truth, self_interact,
                         no_pruning)
    elif encoding == 'lines':
        lines_synthesize(valid, invalid, condition_invalid, ground_truth, self_interact,
                         no_pruning)
    else:
        raise ValueError


def show(valid, invalid, condition_invalid, ground_truth: str):
    print(len(valid), "valid examples:")
    max_len = max(map(lambda x: sum(map(len, x)) + 2 * len(x), valid))
    max_len = max(max_len, 6)
    line_len = 0
    for ex in valid:
        s = ', '.join(ex).center(max_len)
        line_len += len(s)
        print(colored(s, "blue"), end='  ')
        if line_len > 70:
            line_len = 0
            print()
    print()

    print(len(invalid), "invalid examples:")
    max_len = max(map(lambda x: len(x[0]), invalid))
    max_len = max(max_len, 6)
    line_len = 0
    for ex in invalid:
        s = f'{ex[0]}'.center(max_len)
        line_len += len(s)
        print(colored(s, "red"), end='  ')
        if line_len > 70:
            line_len = 0
            print()
    print()

    if len(condition_invalid) > 0:
        print(len(condition_invalid), "condition invalid examples:")
        max_len = max(map(lambda x: len(x[0]), condition_invalid))
        max_len = max(max_len, 6)
        line_len = 0
        for ex in condition_invalid:
            s = f'{ex[0]}'.center(max_len)
            line_len += len(s)
            print(colored(s, "magenta"), end='  ')
            if line_len > 70:
                line_len = 0
                print()
        print()
    else:
        print("No condition invalid examples.")
    print("Ground truth:")
    print(colored(ground_truth, "green"))


def multitree_synthesize(valid: List[List], invalid: List[List],
                         condition_invalid: List[List], ground_truth: str = None,
                         self_interact: bool = False, no_pruning: bool = False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid)
    if "string" not in type_validation[0] and "regex" not in type_validation[0]:
        raise Exception("MultiTree Synthesizer is only for strings.")
    synthesizer = MultiTreeSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                       ground_truth, pruning=not no_pruning,
                                       auto_interaction=self_interact)
    return synthesize(type_validation)


def sketch_synthesize(valid: List[List], invalid: List[List],
                      condition_invalid: List[List], sketching_mode: str,
                      ground_truth: str = None, self_interact: bool = False,
                      no_pruning: bool = False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid,
                                                                    sketch=True)
    if "string" not in type_validation[0] and "regex" not in type_validation[0]:
        raise Exception("MultiTree Synthesizer is only for strings.")
    synthesizer = SketchSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                    ground_truth, sketching_mode,
                                    auto_interaction=self_interact)
    return synthesize(type_validation)


def dynamic_synthesize(valid: List[List], invalid: List[List],
                       condition_invalid: List[List], ground_truth: str = None,
                       self_interact: bool = False, no_pruning: bool = False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid)
    synthesizer = MultiTreeSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                       ground_truth,
                                       pruning=not no_pruning,
                                       auto_interaction=self_interact, force_dynamic=True)
    return synthesize(type_validation)


def ktree_synthesize(valid: List[List], invalid: List[List],
                     condition_invalid: List[List],
                     ground_truth: str = None, self_interact: bool = False,
                     no_pruning: bool = False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid)
    synthesizer = KTreeSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                   ground_truth,
                                   pruning=not no_pruning, auto_interaction=self_interact)
    return synthesize(type_validation)


def lines_synthesize(valid: List[List], invalid: List[List],
                     condition_invalid: List[List],
                     ground_truth: str = None, self_interact: bool = False,
                     no_pruning: bool = False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid)
    synthesizer = LinesSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                   ground_truth,
                                   pruning=not no_pruning, auto_interaction=self_interact)
    return synthesize(type_validation)


def prepare_things(valid, invalid, sketch=False) \
        -> Tuple[TyrellSpec, List[List], List[List], List[List], List[str]]:
    """  returns dsl, valid_examples, invalid_examples, captures, and type_validation """
    type_validation = ["regex"]
    if len(valid) == 0:
        raise ValueError("No valid examples!")
    if isinstance(valid[0], str):
        valid = list(map(lambda v: [v], valid))
    if isinstance(invalid[0], str):
        invalid = list(map(lambda v: [v], invalid))
    # logger.info("Assuming types: " + str(type_validation))
    captures = list(map(lambda x: x[1:], valid))
    valid = list(map(lambda x: [x[0]], valid))
    builder = DSLBuilder(type_validation, valid, invalid, sketch)
    dsl = builder.build()[0]
    # TODO: build() returns a list of DSLs for each different type of element. Now I'm
    #  just using the first element

    return dsl, valid, invalid, captures, type_validation


def synthesize(type_validation):
    global synthesizer
    assert synthesizer is not None
    printer = RegexInterpreter()
    program = synthesizer.synthesize()
    if program is not None:
        regex, captures, conditions, condition_captures = program
        solution_str = printer.eval(regex, captures=condition_captures)
        solution_str += ', ' + conditions_to_str(conditions)
        print(f'\nSolution:\n  {solution_str}\n'
              f'Captures:\n  {printer.eval(regex, captures=captures)}')
    else:
        print('Solution not found!')
    return program


# noinspection PyTypeChecker
def read_cmd_args():
    encodings = ('multitree', 'dynamic', 'ktree', 'lines')
    sketching = ('none', 'smt', 'brute-force', 'hybrid')
    parser = argparse.ArgumentParser(description='Validations Synthesizer',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('file', type=str, help='File with I/O examples.')
    parser.add_argument('-d', '--debug', action='store_true', help='Debug mode.')
    parser.add_argument('-e', '--encoding', metavar='|'.join(encodings), type=str,
                        default='multitree', help='SMT encoding.')
    parser.add_argument('-s', '--self-interact', action="store_true",
                        help="Self interaction mode.")
    parser.add_argument('--no-pruning', '--nopruning', action='store_true',
                        help='Disable pruning.')
    parser.add_argument('--resnax', action='store_true',
                        help='Read resnax i/o examples format.')
    parser.add_argument('-v', '--max-valid', type=int, default=-1,
                        help='Limit the number of valid examples. -1: unlimited.')
    parser.add_argument('-i', '--max-invalid', type=int, default=-1,
                        help='Limit the number of invalid examples. -1: unlimited.')
    parser.add_argument('-k', '--sketch', metavar='|'.join(sketching), type=str,
                        default='none', help='Enable sketching.')
    args = parser.parse_args()
    if args.debug:
        logger.setLevel("DEBUG")
    else:
        logger.setLevel("INFO")
    if args.encoding not in encodings:
        raise ValueError('Unknown encoding ' + args.encoding)

    return args.file, args.encoding, args.self_interact, args.resnax, args.no_pruning, \
           args.max_valid, args.max_invalid, args.sketch


if __name__ == '__main__':
    main()
