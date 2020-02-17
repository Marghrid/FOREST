import glob
import subprocess
import os

instances = []
for file in glob.glob("instances/strings/*.txt"):
    instances.append(file)
commands = [["runsolver", "-W", "60", "python3", "validate.py", "-f", instance] for instance in instances]

processes = []

for command in commands:
    process = subprocess.Popen(command,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    processes.append((process, command))
    
for task in processes:
    process = task[0]
    instance = task[1][-1]
    print("\n=====  " + instance + "  =====")
    try:
        process.wait(timeout=120)
    except subprocess.TimeoutExpired:
        print("timeout")
        continue
    po, pe = process.communicate()
    po = str(po, encoding ='utf-8').splitlines()
    pe = str(pe, encoding ='utf-8').splitlines()
    for l in po + pe:
        if "Real time" in l:
            print(l)
