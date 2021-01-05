#!/bin/bash
timeout=$1
log_prefix=${2-${log_prefix}}

if [ $# -eq 0 ]; then
    echo "Usage: ${0} TIMEOUT_IN_SECONDS [LOG_PREFIX]".  
    exit 1
fi


# default setting:
python3 scripts/make_table.py ${log_prefix}_mt > info_${timeout}_mt 

# Multi-tree encoding without pruning:
python3 scripts/make_table.py ${log_prefix}_np > info_${timeout}_np 

# Dynamic-only muti-tree encoding:
python3 scripts/make_table.py ${log_prefix}_dy > info_${timeout}_dy 

# k-tree encoding:
python3 scripts/make_table.py ${log_prefix}_kt > info_${timeout}_kt 

# Line-based encoding
python3 scripts/make_table.py ${log_prefix}_li > info_${timeout}_li 

# 5 examples of each kind only
python3 scripts/make_table.py ${log_prefix}_05 > info_${timeout}_05 

# 10 examples of each kind only
python3 scripts/make_table.py ${log_prefix}_10 > info_${timeout}_10

