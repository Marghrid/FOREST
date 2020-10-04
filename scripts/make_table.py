import argparse
import glob
import re
from typing import List

print_columns = ["name", "enumerator", "timed_out", "total_synthesis_time", "regex_synthesis_time",
                 "first_regex_time", "enumerated_regexes", "regex_interactions",
                 "regex_distinguishing_time", "cap_groups_synthesis_time", "enumerated_cap_groups",
                 "cap_conditions_synthesis_time", "enumerated_cap_conditions",
                 "cap_conditions_interactions", "cap_conditions_distinguishing_time", "solution",
                 "first_regex", "cap_groups", "ground_truth"]

regel_columns = ["regel_time", "regel_timeout", "regel_sketch", "regel_solution"]

all_columns = ["name", "enumerator", "timed_out", "total_synthesis_time", "regex_synthesis_time",
               "first_regex_time", "enumerated_regexes", "regex_interactions",
               "regex_distinguishing_time", "cap_groups_synthesis_time", "enumerated_cap_groups",
               "cap_conditions_synthesis_time", "enumerated_cap_conditions",
               "cap_conditions_interactions", "cap_conditions_distinguishing_time", "solution",
               "first_regex", "cap_groups", "ground_truth", "regel_time", "regel_timeout",
               "regel_sketch", "regel_solution"]


class Instance:
    def __init__(self, name):
        global all_columns
        self.values = {}
        for col in all_columns:
            self.values[col] = "undefined"
        self.values['name'] = name


def print_table(instances: List, regel: bool):
    """ Print execution information for each instance (sorted by name) """
    global print_columns, regel_columns

    if regel:
        print_columns.extend(regel_columns)

    print(", ".join(print_columns))

    for instance in instances:
        row = []
        for col_name in print_columns:
            if col_name in ["solution", "cap_groups", "ground_truth", "regel_sketch", "regel_solution"]:
                row.append(f'"{instance.values[col_name]}"')
            else:
                row.append(str(instance.values[col_name]))
        print(', '.join(row))


def main():
    parser = argparse.ArgumentParser(description='Validations Synthesizer tester',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('log_dir', metavar='DIR', type=str, help="Logs directory", default='')
    parser.add_argument('-r', '--regel-log-dir', metavar='DIR', type=str,
                        help="Regel logs directory", default='')

    args = parser.parse_args()

    log_dir = args.log_dir
    regel_log_dir = args.regel_log_dir

    log_files = glob.glob(log_dir + "/*.txt")
    instances = []

    for log_file in log_files:
        instance_name = list(filter(None, log_file.split('/')))[-1]
        instance = Instance(instance_name)
        instances.append(instance)
        with open(log_file) as f:
            regex_synthesis = False
            cap_groups_synthesis = False
            cap_conditions_synthesis = False
            solution_print = False
            for line in f:
                if "Enumerator" in line:
                    regex = "Enumerator: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['enumerator'] = m[1]
                elif "Terminated" in line:
                    regex = "Terminated: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['timed_out'] = m[1] == 'True'
                elif "Elapsed time" in line:
                    regex = r"Elapsed time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['total_synthesis_time'] = float(m[1])
                elif "Time per depth" in line:
                    regex = "Time per depth: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['per_depth_times'] = m[1]
                elif "Regex synthesis" in line:
                    regex_synthesis = True
                    continue
                elif "Capturing groups synthesis" in line:
                    regex_synthesis = False
                    cap_groups_synthesis = True
                    continue
                elif "Capturing conditions synthesis" in line:
                    cap_groups_synthesis = False
                    cap_conditions_synthesis = True
                    continue
                elif "First regex" in line:
                    regex = r"First regex: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['first_regex'] = m[1]
                elif "Solution" in line:
                    cap_conditions_synthesis = False
                    solution_print = True
                    regex = r"Solution: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['solution'] = m[1]
                    continue
                elif "No solution" in line:
                    cap_conditions_synthesis = False
                    solution_print = True
                    instance.values['solution'] = 'No solution'
                    instance.values['cap_groups'] = None
                    continue

                elif regex_synthesis:
                    if "Regex time" in line:
                        regex = r"Regex time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['regex_synthesis_time'] = float(m[1])
                    elif "First regex time" in line:
                        regex = r"First regex time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['first_regex_time'] = float(m[1])
                    elif "Enumerated" in line:
                        regex = r"Enumerated: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['enumerated_regexes'] = int(m[1])
                    elif "Interactions" in line:
                        regex = r"Interactions: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['regex_interactions'] = int(m[1])
                    elif "Distinguish time" in line:
                        regex = r"Distinguish time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['regex_distinguishing_time'] = float(m[1])

                elif cap_groups_synthesis:
                    if "Cap. groups time" in line:
                        regex = r"Cap. groups time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['cap_groups_synthesis_time'] = float(m[1])
                    elif "Enumerated" in line:
                        regex = r"Enumerated: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['enumerated_cap_groups'] = int(m[1])

                elif cap_conditions_synthesis:
                    if "Cap. conditions time" in line:
                        regex = r"Cap. conditions time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['cap_conditions_synthesis_time'] = float(m[1])
                    elif "Enumerated" in line:
                        regex = r"Enumerated: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['enumerated_cap_conditions'] = int(m[1])
                    elif "Interactions" in line:
                        regex = r"Interactions: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['cap_conditions_interactions'] = int(m[1])
                    elif "Distinguish time" in line:
                        regex = r"Distinguish time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['cap_conditions_distinguishing_time'] = float(m[1])

                elif solution_print:
                    if "Nodes" in line:
                        regex = r"Nodes: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['nodes'] = int(m[1])
                    elif "No capturing groups" in line:
                        instance.values['cap_groups'] = None
                    elif "Cap. groups" in line:
                        regex = r"Cap\. groups: (.+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['cap_groups'] = m[1]
                    elif "Num. cap. groups" in line:
                        regex = r"Num\. cap\. groups: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['num_cap_groups'] = m[1]
                    elif "Ground truth" in line:
                        regex = r"Ground truth: (.+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['ground_truth'] = m[1]

    if len(regel_log_dir) > 0:
        for instance in instances:
            try:
                with open(regel_log_dir + "/" + instance.values['name'] + "-1") as f:
                    for line in f:
                        if "Sketch" in line:
                            regex = r"Sketch: (.+)"
                            m = re.search(regex, line)
                            if m is not None:
                                instance.values["regel_sketch"] = m[1]
                        elif "Learned program" in line:
                            regex = r"Learned program: (.+): (?:\d+\.\d+)"
                            m = re.search(regex, line)
                            if m is not None:
                                instance.values["regel_solution"] = m[1]
                        elif "Total time" in line:
                            regex = r"Total time: (\d+\.\d+)"
                            m = re.search(regex, line)
                            if m is not None:
                                instance.values['regel_time'] = float(m[1])
                                instance.values['regel_timeout'] = False
            except IOError:
                try:
                    with open(regel_log_dir + "/" + instance.values['name'] + "-b") as f:
                        for line in f:
                            if "Total time" in line:
                                regex = r"Total time: (\d+\.\d+)"
                                m = re.search(regex, line)
                                if m is not None:
                                    instance.values['regel_time'] = float(m[1])
                                    instance.values['regel_timeout'] = False
                except:
                    print("could not open", regel_log_dir + "/" + instance.values['name'] + "-1")

    instances = sorted(instances, key=lambda i: i.values['name'])
    print_table(instances, len(regel_log_dir) > 0)


if __name__ == '__main__':
    main()
