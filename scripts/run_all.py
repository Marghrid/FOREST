#!/usr/bin/env python3
import glob
import re
import subprocess
from termcolor import colored

def chunks(lst, n):
    """Yield successive n-sized chunks from lst."""
    for i in range(0, len(lst), n):
        yield lst[i:i + n]


run_each = 2
num_processes = 12

instances_dir = "instances/strings/"
if instances_dir[-1] != '/':
    instances_dir += '/'
command_base = ["runsolver", "-W", "600", "python3", "validate.py", "-f"]

instances = glob.glob(instances_dir + "*.txt")

instance_times = {i: [] for i in instances}
instance_enumerated = {i: [] for i in instances}

for chunk in chunks(instances, num_processes // run_each):
    tasks = []
    for instance in chunk:
        command = command_base + [instance]

        for i in range(run_each):
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            tasks.append((command, process))

    for task in tasks:
        command = task[0]
        instance = command[-1]

        process = task[1]
        inst_name = instance.replace(instances_dir, "", 1)
        inst_name = inst_name.replace(".txt", "", 1)
        process.wait()
        po, pe = process.communicate()
        po = str(po, encoding='utf-8').splitlines()
        pe = str(pe, encoding='utf-8').splitlines()
        time = -1
        enumerated = -1
        for l in po + pe:
            if "Maximum wall clock time exceeded:" in l:
                print(colored("\n=====  " + inst_name + "timed out.  =====", "red"))
                break
            if "Real time" in l:
                time = l.replace("Real time (s):", " ", 1)
                time = float(time)
            if "attempts" in l:
                regex = "(\\d+) attempts"
                enumerated = int(re.search(regex, l)[1])
        if time > -1:
            instance_times[instance].append(time)
            instance_enumerated[instance].append(enumerated)
        print(colored("\n=====  " + inst_name + "  =====", "blue"))
        print(time, "s")
        print("enumerated", enumerated)

        tasks = []

# ================

for inst in instances:
    times = instance_times[inst]
    if len(times) > 0:
        avg_time = sum(times) / len(times)
    else:
        avg_time = -1
    print("avg time:", avg_time, "s")
    instance_times[inst] = round(avg_time)

    enumerated = instance_enumerated[inst]
    if len(enumerated) > 0 and all([el == enumerated[0] for el in enumerated]):
        instance_enumerated[inst] = enumerated[0]
    else:
        instance_enumerated[inst] = -1

print("\n======= Final =======")
for instance in instance_times:
    inst_name = instance.replace(instances_dir, "", 1)
    inst_name = inst_name.replace(".txt", "", 1)
    print(f"{inst_name}: {instance_times[instance]}s, enumerated {instance_enumerated[instance]}")
print('All OK - GREAT SUCCESS')
