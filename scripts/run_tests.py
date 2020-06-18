#!/usr/bin/env python3

import argparse
from signal import signal, SIGINT

from tester import Tester

tester = None


def handler(signal_received, frame):
    # Handle any cleanup here
    print('\nSIGINT or CTRL-C detected. Exiting gracefully.')
    if tester is not None:
        tester.terminate_all()
        tester.print_results()
    exit()


# noinspection PyTypeChecker
def main():
    signal(SIGINT, handler)
    encodings = ('multitree', 'dynamic', 'ktree', 'lines', 'compare-times')
    sketching = ('none', 'smt', 'brute-force', 'hybrid')

    parser = argparse.ArgumentParser(description='Validations Synthesizer tester',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('directories', type=str, metavar="dir", nargs='+',
                        help='Directories with instances')
    parser.add_argument('-p', '--processes', metavar="P", type=int,
                        help='Number of processes.', default=1)
    parser.add_argument('-r', '--run-each', metavar="R", type=int,
                        help='Number of times to run each instance.', default=1)
    parser.add_argument('-t', '--timeout', metavar="T", type=int,
                        help='Timeout in seconds.', default=120)
    parser.add_argument('-o', '--out', action='store_true',
                        help='Show output.', default=False)
    parser.add_argument('-l', '--solve-only', type=int, default=-1,
                             help='Limit the number of solved instances. -1: unlimited.')

    synth_group = parser.add_argument_group(title="Synthesizer options")
    synth_group.add_argument('-e', '--encoding', metavar='|'.join(encodings), type=str,
                        default='multitree', help='SMT encoding.')
    synth_group.add_argument('--resnax', action='store_true',
                        help='read resnax i/o examples format.')
    synth_group.add_argument('--no-pruning', '--nopruning', action='store_true',
                             help='read resnax i/o examples format.')
    synth_group.add_argument('-v', '--max-valid', type=int, default=-1,
                        help='Limit the number of valid examples. -1: unlimited.')
    synth_group.add_argument('-i', '--max-invalid', type=int, default=-1,
                        help='Limit the number of invalid examples. -1: unlimited.')

    synth_group.add_argument('-k', '--sketch', metavar='|'.join(sketching), type=str,
                        default='none', help='Enable sketching.')

    args = parser.parse_args()

    if args.encoding not in encodings:
        raise ValueError('Unknown encoding ' + args.encoding)

    global tester

    tester = Tester(args.directories, args.encoding, args.no_pruning, args.sketch,
                    args.processes, args.run_each, args.timeout, args.out, args.resnax,
                    args.max_valid, args.max_invalid, args.solve_only)
    tester.test()
    if args.encoding == 'compare-times':
        tester.print_time_comparison()
    else:
        tester.print_results()


if __name__ == '__main__':
    main()
