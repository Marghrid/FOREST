#!/bin/bash
timeout=$1
log_prefix=${2-log_${timeout}}

if [ $# -eq 0 ]; then
    echo "Usage: ${0} TIMEOUT_IN_SECONDS [LOG_PREFIX]".  
    exit 1
fi

for n in "mt" "np" "dy" "kt" "li" "05" "10"
do
	if [[ -d "${log_prefix}_${n}" ]]
	then
	    echo "${log_prefix}_${n} exists. Please delete it or define another log prefix."
	    exit 1
	fi
	# mkdir  ${log_prefix}_${n} 
done


# default setting:
python3 scripts/run_benchmarks.py -t ${timeout} -p 1            --log ${log_prefix}_mt  benchmarks/

# Multi-tree encoding without pruning:
python3 scripts/run_benchmarks.py -t ${timeout} -p 1 -e multitree --nopruning --log ${log_prefix}_np  benchmarks/

# Dynamic-only muti-tree encoding:
python3 scripts/run_benchmarks.py -t ${timeout} -p 1 -e dynamic --log ${log_prefix}_dy  benchmarks/

# k-tree encoding:
python3 scripts/run_benchmarks.py -t ${timeout} -p 1 -e ktree   --log ${log_prefix}_kt  benchmarks/

# Line-based encoding
python3 scripts/run_benchmarks.py -t ${timeout} -p 1 -e lines   --log ${log_prefix}_li  benchmarks/

# 5 examples of each kind only
python3 scripts/run_benchmarks.py -t ${timeout} -p 1 -m 5       --log ${log_prefix}_05  benchmarks/

# 10 examples of each kind only
python3 scripts/run_benchmarks.py -t ${timeout} -p 1 -m 10      --log ${log_prefix}_10  benchmarks/

