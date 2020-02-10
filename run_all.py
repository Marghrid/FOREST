import glob
import subprocess
import os

txtfiles = []
for file in glob.glob("instances/*.txt"):
    txtfiles.append(file)
processes = []

for instance in txtfiles:
    process = subprocess.Popen(["python3", "validate.py", "-f", instance],
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    processes.append((process, instance))
    
for task in processes:
    process = task[0]
    instance = task[1]
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
        print(l)
