#!/usr/bin/env python3
import glob
import re
import subprocess
from termcolor import colored

def chunks(lst, n):
	""" Yield successive n-sized chunks from lst. """
	for i in range(0, len(lst), n):
		yield lst[i:i + n]

# If num_processes < 2*run_each, then run_each = 1.
run_each = 2
num_processes = 1
timeout = 60

instances_dirs = ["instances/strings/ambiguous/", "instances/strings/"]
command_base = ["time", "python3", "validate.py", "-f"]

instances = []
for instances_dir in instances_dirs:
	instances += glob.glob(instances_dir + "/*.txt")

print("=====  Found instances:  =====")
for inst in instances:
	print(inst)


instance_times = {i.split("/")[-1].replace(".txt", "", 1):[] for i in instances}
instance_enumerated = {i:[] for i in instances}

chunk_size = max(num_processes//run_each, 1)


for chunk in chunks(instances, chunk_size):
	tasks = []
	for instance in chunk:
		command = command_base + [instance]
		
		for i in range(run_each):
			process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
			tasks.append((command, process))

	for task in tasks:
		command = task[0]
		instance = command[-1]
		inst_name = instance.split("/")[-1]
		inst_name = inst_name.replace(".txt", "", 1)

		process = task[1]
		try:
			process.wait(timeout=timeout)
		except subprocess.TimeoutExpired:
			print("timeout")
			continue
		po, pe = process.communicate()
		po = str(po, encoding ='utf-8').splitlines()
		pe = str(pe, encoding ='utf-8').splitlines()
		time = -1
		enumerated = -1
		solution = ''
		for l in po + pe:
			if "real" in l:
				regex = r"(\d+\.\d+) real"
				time = float(re.search(regex, l)[1])
			if "attempts" in l:
				regex = "(\\d+) attempts"
				enumerated = int(re.search(regex, l)[1])
			if "Solution found:" in l:
				solution = l.replace("[info] Solution found: ", "", 1)

		if time > -1:
			instance_times[inst_name].append(time)
			instance_enumerated[instance].append(enumerated)
		print(colored("\n=====  " + inst_name + "  =====", "blue"))
		print(time, "s")
		print("enumerated", enumerated)
		print("solution", solution)

		tasks = []


# ================

for inst in instances:
	inst_name = inst.split("/")[-1]
	inst_name = inst_name.replace(".txt", "", 1)
	times = instance_times[inst_name]
	if len(times) > 0:
		avg_time = sum(times) / len(times)
	else:
		avg_time = -1
	instance_times[inst_name] = round(avg_time)

	enumerated = instance_enumerated[inst]
	if len(enumerated) > 0 and all([el == enumerated[0] for el in enumerated]):
		instance_enumerated[inst] = enumerated[0]
	else:
		instance_enumerated[inst] = -1


print("\n======= Final =======")
for instance in sorted(instance_enumerated):
	inst_name = instance.split("/")[-1]
	inst_name = inst_name.replace(".txt", "", 1)
	print(f"{inst_name}: {instance_times[inst_name]}s, enumerated {instance_enumerated[instance]}")
print('All OK - GREAT SUCCESS')

