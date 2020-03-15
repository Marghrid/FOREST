import glob
import random
import re
import subprocess
from termcolor import colored


class Instance:
    def __init__(self, name, path):
        self.name = name
        self.path = path
        self.tasks = []

    def add_task(self, task):
        self.tasks.append(task)

    def kill_tasks(self):
        for t in self.tasks:
            t.kill()

    def __str__(self):
        return self.name


class Task:
    def __init__(self, command, instance, timeout):
        self.command = command
        self.instance = instance
        self.instance.add_task(self)
        self.timeout = timeout
        self.process = None

        self.time = -1
        self.enumerated = -1
        self.interactions = -1
        self.solution = ''

    def run(self):
        print(colored(f"Running {self.instance}.", "blue"))
        interaction_file = open('interaction.txt')
        self.process = subprocess.Popen(self.command, stdin=interaction_file,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def kill(self):
        if self.process is not None:
            self.process.kill()

    def wait(self, show_output):
        print(colored(f"Waiting for {self.instance}.", "cyan"))
        try:
            self.process.wait(timeout=self.timeout)
        except subprocess.TimeoutExpired:
            print(colored(f"{self.instance} timed out.", "red"))
            self.instance.kill_tasks()
            return

        po, pe = self.process.communicate()
        po = str(po, encoding='utf-8').splitlines()
        pe = str(pe, encoding='utf-8').splitlines()

        for l in po + pe:
            # print(l)
            if re.search("[\w+]", l) is not None and show_output:
                print(" ", l)
            if "elapsed" in l:
                regex = r"elapsed: (\d+) seconds"
                self.time = int(re.search(regex, l)[1])
            if "attempts" in l:
                regex = "(\\d+) attempts"
                self.enumerated = int(re.search(regex, l)[1])
            if "interactions" in l:
                regex = "(\\d+) interactions"
                self.interactions = int(re.search(regex, l)[1])
            if "Solution:" in l:
                self.solution = l.replace("[info] Solution: ", "", 1)
        #
        # print(colored("\n=====  " + inst_name + "  =====", "blue"))
        # print(time, "s")
        # print("enumerated", enumerated)
        # print("solution:", solution)


class Tester:
    def __init__(self, instance_dirs, num_processes=1, run_each=1, timeout=120, runsolver=False, show_output=False):
        # several per instance. Len = len(instances) * run_each
        self.show_output = show_output
        self.tasks = []
        self.instances = []
        self.num_processes = num_processes
        if runsolver:
            command_base = ["runsolver", "-W", str(timeout), "python3", "multipleValidate.py", "-f"]
        else:
            command_base = ["python3", "multipleValidate.py", "-f"]

        for dir in instance_dirs:
            instance_paths = glob.glob(dir + "/*.txt")

            for inst_path in instance_paths:
                inst_name = inst_path.split("/")[-1]
                inst_name = inst_name.replace(".txt", "", 1)
                self.instances.append(Instance(inst_name, inst_path))

        # instances are sorted by name
        self.instances = sorted(self.instances, key=lambda i: i.name)

        for inst in self.instances:
            for i in range(run_each):
                command = command_base + [inst.path]
                new_task = Task(command=command, instance=inst, timeout=timeout)
                self.tasks.append(new_task)

        # tasks are ordered randomly
        random.shuffle(self.tasks)

    def chunks(self, lst, n):
        """ Yield successive n-sized chunks from lst. """
        for i in range(0, len(lst), n):
            yield lst[i:i + n]

    def test(self):
        """ Starts running tasks in random order """
        for chunk in self.chunks(self.tasks, self.num_processes):
            for task in chunk:
                task.run()

            for task in chunk:
                task.wait(self.show_output)

    def print_results(self):
        """ Print execution information for each instance (sorted by name) """
        maxl = max(map(lambda i: len(i.name), self.instances)) + 2
        print("\n =====  RESULTS  ===== ")
        for inst in self.instances:
            times = [t.time for t in inst.tasks]
            enumerated = [t.enumerated for t in inst.tasks]
            interactions = [t.interactions for t in inst.tasks]

            times = list(filter(lambda x: x > 0, times))
            enumerated = list(filter(lambda x: x > 0, enumerated))
            interactions = list(filter(lambda x: x >= 0, interactions))

            if len(times) == 0:
                print(f"{inst.name}:".ljust(maxl), "timed out")
            elif any(x != enumerated[0] for x in enumerated):
                print(f"{inst.name}:".ljust(maxl), "does not always enumerate the same number of programs")
            else:
                print(f"{inst.name}:".ljust(maxl),
                      f"avg time {round(sum(times) / len(times))}s,".ljust(15),
                      f"avg int {round(sum(interactions) / len(interactions))},".ljust(11),
                      f"enum {enumerated[0]},".ljust(11),
                      f"sol {inst.tasks[0].solution}")
