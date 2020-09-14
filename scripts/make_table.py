import argparse
import glob
import re
from typing import List


class Instance:
    def __init__(self, name):
        self.name = name

        self.enumerator = "En"
        self.timed_out = False
        self.nodes = -1
        self.solution = 'Sol'
        self.cap_groups = 'CG'
        self.num_cap_groups = -1
        self.ground_truth = 'GT'

        # timers:
        self.total_synthesis_time = -1
        self.per_depth_times = {}

        self.regex_synthesis_time = -1
        self.cap_groups_synthesis_time = -1
        self.cap_conditions_synthesis_time = -1

        self.first_regex_time = -1

        self.regex_distinguishing_time = -1
        self.cap_conditions_distinguishing_time = -1

        # enumerated
        self.enumerated_regexes = -1
        self.enumerated_cap_groups = -1
        self.enumerated_cap_conditions = -1

        # interactions
        self.regex_interactions = -1
        self.cap_conditions_interactions = -1

        # regel
        self.regel_time = -1
        self.regel_timeout = True


def print_table(instances: List, regel: bool):
    """ Print execution information for each instance (sorted by name) """
    # maxl = max(map(lambda i: len(i.name), self.instances)) + 2
    # max_enumerators_length = max(map(lambda t: len(t.enumerator), self.tasks)) + 2
    # max_enumerated_length = max(map(lambda t: len(str(t.enumerated)), self.tasks)) + 2
    columns = ["instance", "timed out", "total time", "regex time", "first regex time",
               "enumerated regexes", "regex interactions", "regex distinguish time",
               "cap groups time", "enumerated cap groups", "cap conditions time",
               "enumerated cap conditions", "cap cond interactions", "cap cond distinguish time",
               "solution", "cap groups", "ground truth"]
    if regel:
        columns.extend(["regel time", "regel_timeout"])

    print(", ".join(columns))

    for instance in instances:
        print(
            f'{instance.name}, '
            f'{int(instance.timed_out)}, '
            f'{instance.total_synthesis_time}, '
            f'{instance.regex_synthesis_time}, '
            f'{instance.first_regex_time}, '
            f'{instance.enumerated_regexes}, '
            f'{instance.regex_interactions}, '
            f'{instance.regex_distinguishing_time}, '
            f'{instance.cap_groups_synthesis_time}, '
            f'{instance.enumerated_cap_groups}, '
            f'{instance.cap_conditions_synthesis_time}, '
            f'{instance.enumerated_cap_conditions}, '
            f'{instance.cap_conditions_interactions}, '
            f'{instance.cap_conditions_distinguishing_time}, '
            f'"{instance.solution}", "{instance.cap_groups}", '
            f'"{instance.ground_truth}"', end=''
        )
        if regel:
            print(f', {instance.regel_time}, {int(instance.regel_timeout)}')
        else:
            print()


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
                        instance.enumerator = m[1]
                elif "Terminated" in line:
                    regex = "Terminated: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.timed_out = m[1] == 'True'
                elif "Elapsed time" in line:
                    regex = r"Elapsed time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.total_synthesis_time = float(m[1])
                elif "Time per depth" in line:
                    regex = "Time per depth: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.per_depth_times = m[1]
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
                elif "Solution" in line:
                    cap_conditions_synthesis = False
                    solution_print = True
                    regex = r"Solution: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.solution = m[1]
                    continue

                elif regex_synthesis:
                    if "Regex time" in line:
                        regex = r"Regex time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.regex_synthesis_time = float(m[1])
                    elif "First regex time" in line:
                        regex = r"First regex time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.first_regex_time = float(m[1])
                    elif "Enumerated" in line:
                        regex = r"Enumerated: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.enumerated_regexes = int(m[1])
                    elif "Interactions" in line:
                        regex = r"Interactions: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.regex_interactions = int(m[1])
                    elif "Distinguish time" in line:
                        regex = r"Distinguish time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.regex_distinguishing_time = float(m[1])

                elif cap_groups_synthesis:
                    if "Cap. groups time" in line:
                        regex = r"Cap. groups time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.cap_groups_synthesis_time = float(m[1])
                    elif "Enumerated" in line:
                        regex = r"Enumerated: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.enumerated_cap_groups = int(m[1])

                elif cap_conditions_synthesis:
                    if "Cap. conditions time" in line:
                        regex = r"Cap. conditions time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.cap_conditions_synthesis_time = float(m[1])
                    elif "Enumerated" in line:
                        regex = r"Enumerated: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.enumerated_cap_conditions = int(m[1])
                    elif "Interactions" in line:
                        regex = r"Interactions: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.cap_conditions_interactions = int(m[1])
                    elif "Distinguish time" in line:
                        regex = r"Distinguish time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.cap_conditions_distinguishing_time = float(m[1])

                elif solution_print:
                    if "Nodes" in line:
                        regex = r"Nodes: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.nodes = int(m[1])
                    elif "No capturing groups" in line:
                        instance.cap_groups = None
                    elif "Cap. groups" in line:
                        regex = r"Cap\. groups: (.+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.cap_groups = m[1]
                    elif "Num. cap. groups" in line:
                        regex = r"Num\. cap\. groups: (\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.num_cap_groups = m[1]
                    elif "Ground truth" in line:
                        regex = r"Ground truth: (.+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.ground_truth = m[1]
                            print(instance.ground_truth)

    if len(regel_log_dir) > 0:
        for instance in instances:
            try:
                with open(regel_log_dir + "/" + instance.name + "-1") as f:
                    for line in f:
                        if "Total time" in line:
                            regex = r"Total time: (\d+\.\d+)"
                            m = re.search(regex, line)
                            if m is not None:
                                instance.regel_time = float(m[1])
                                instance.regel_timeout = False
            except IOError:
                print("could not open", regel_log_dir + "/" + instance.name + "-1")

    instances = sorted(instances, key=lambda i: i.name)
    print_table(instances, len(regel_log_dir) > 0)


if __name__ == '__main__':
    main()
