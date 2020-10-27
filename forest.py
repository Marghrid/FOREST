#!/usr/bin/env python3
import argparse
import os
import random
from signal import signal, SIGINT, SIGTERM
from forest.configuration import Configuration
from forest.logger import get_logger
from forest.parse_examples import parse_file, parse_resnax, show, preprocess
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
        synthesizer.configuration.die = True


def main():
    signal(SIGINT, sig_handler)
    signal(SIGTERM, sig_handler)
    examples_file, resnax, max_valid, max_invalid, config = read_cmd_args()

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

    global synthesizer
    dsl, valid, invalid, captures, type_validation = preprocess(valid, invalid)
    if config.sketching != 'none':
        dsl, valid, invalid, captures, type_validation = preprocess(valid, invalid, sketch=True)
        if "string" not in type_validation[0] and "regex" not in type_validation[0]:
            raise Exception("MultiTree Synthesizer is only for strings.")
        synthesizer = SketchSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                        ground_truth, configuration=config)
    elif config.encoding == 'multitree':
        if "string" not in type_validation[0] and "regex" not in type_validation[0]:
            raise Exception("MultiTree Synthesizer is only for strings.")
        synthesizer = MultiTreeSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                           ground_truth, configuration=config)
    elif config.encoding == "dynamic":
        config.force_dynamic = True
        synthesizer = MultiTreeSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                           ground_truth, configuration=config)
    elif config.encoding == 'ktree':
        synthesizer = KTreeSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                       ground_truth, configuration=config)
    elif config.encoding == 'lines':
        synthesizer = LinesSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                       ground_truth, configuration=config)

    else:
        raise ValueError

    return synthesize(type_validation)

def synthesize(type_validation):
    global synthesizer
    assert synthesizer is not None
    printer = RegexInterpreter()
    program = synthesizer.synthesize()
    if program is not None:
        regex, capturing_groups, capture_conditions = program
        conditions, condition_captures = capture_conditions
        solution_str = printer.eval(regex, captures=condition_captures)
        solution_str += ', ' + conditions_to_str(conditions)
        print(f'\nSolution:\n  {solution_str}')
        if len(capturing_groups) > 0:
            print(f'Captures:\n  {printer.eval(regex, captures=capturing_groups)}')
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
    parser.add_argument('-l', '--log', metavar='DIR', type=str, default='', help='Logs directory')
    parser.add_argument('-s', '--self-interact', action="store_true",
                        help="Self interaction mode.")
    parser.add_argument('--no-pruning', '--nopruning', action='store_true',
                        help='Disable pruning.')
    parser.add_argument('--no-captures', '--nocaptures', action='store_true',
                             help='Disable synthesis of capturing groups.')
    parser.add_argument('--no-conditions', '--noconditions', action='store_true',
                             help='Disable synthesis of capture conditions.')
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
    if args.sketch not in sketching:
        raise ValueError('Unknown sketching mode ' + args.encoding)

    if len(args.log) > 0:
        if not os.path.exists(args.log):
            os.makedirs(args.log)

    examples_filename = list(filter(None, args.file.split('/')))[-1]

    if len(args.log) > 0:
        # Clean up existing log file
        log_path = args.log + "/" + examples_filename
        if os.path.exists(log_path):
            os.remove(log_path)
        open(log_path, "w")
    else:
        log_path = ''

    config = Configuration(encoding=args.encoding, self_interact=args.self_interact,
                           log_path=log_path, pruning=not args.no_pruning,
                           synth_captures = not args.no_captures,
                           synth_conditions = not args.no_conditions, sketching=args.sketch)
    config.print_first_regex = True

    return args.file, args.resnax, args.max_valid, args.max_invalid, config


if __name__ == '__main__':
    main()
