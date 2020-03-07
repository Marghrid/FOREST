#!/usr/bin/env python3

import argparse

from tester import Tester

def main():

    parser = argparse.ArgumentParser(description='Validations Synthesizer tester')
    parser.add_argument('directories', type=str, metavar="dir", nargs='+', help='Directories with instances')
    parser.add_argument('-p', '--processes', metavar="P", type=int, help='Number of processes. Default: 1.', default=1)
    parser.add_argument('-r', '--run-each', metavar="R", type=int,
                        help='Number of times to run each instance. Default: 1.', default=1)
    parser.add_argument('-t', '--timeout', metavar="T", type=int, help='Timeout in seconds. Default: 120.', default=120)
    parser.add_argument('-o', '--out', action='store_true', help='Show output. Default: False.', default=False)
    args = parser.parse_args()

    num_processes = args.processes
    run_each = args.run_each
    timeout = args.timeout
    show_output = args.out

    tester = Tester(args.directories, num_processes, run_each, timeout, False, show_output)
    tester.test()
    tester.print_results()


if __name__ == '__main__':
    main()