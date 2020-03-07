#!/usr/bin/env python3

import argparse

from tester import Tester

def main():

    parser = argparse.ArgumentParser(description='Validations Synthesizer tester')
    parser.add_argument('directories', type=str, metavar="dir", nargs='+', help='Directories with')
    parser.add_argument('-p', '--processes', type=int, help='Number of processes')
    parser.add_argument('-r', '--run-each', type=int, help='Number of times to run each instance')
    parser.add_argument('-t', '--timeout', type=int, help='Timeout in seconds')
    parser.add_argument('-o', '--out', action='store_true', help='Show output')
    args = parser.parse_args()

    # defaults:
    num_processes=1
    run_each=1
    timeout=120
    runsolver=False
    show_output=False

    if args.processes:
        num_processes = args.processes
    if args.run_each:
        run_each = args.run_each
    if args.timeout:
        timeout = args.timeout
    if args.out:
        show_output = args.show_output

    tester = Tester(args.directories, num_processes, run_each, timeout, False, show_output)
    tester.test()
    tester.print_results()


if __name__ == '__main__':
    main()