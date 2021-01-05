#!/bin/bash
timeout=$1
log_prefix=${2-log_${timeout}}

if [ $# -eq 0 ]; then
    echo "Usage: ${0} TIMEOUT_IN_SECONDS [LOG_PREFIX]".  
    exit 1
fi


# default setting:
python scripts/make_table.py --rank ${log_prefix}_mt > cactus_${timeout}_mt.csv

# Multi-tree encoding without pruning:
python scripts/make_table.py --rank ${log_prefix}_np > cactus_${timeout}_np.csv

# Dynamic-only muti-tree encoding:
python scripts/make_table.py --rank ${log_prefix}_dy > cactus_${timeout}_dy.csv

# k-tree encoding:
python scripts/make_table.py --rank ${log_prefix}_kt > cactus_${timeout}_kt.csv

# Line-based encoding
python scripts/make_table.py --rank ${log_prefix}_li > cactus_${timeout}_li.csv

# 5 examples of each kind only
python scripts/make_table.py --rank ${log_prefix}_05 > cactus_${timeout}_05.csv

# 10 examples of each kind only
python scripts/make_table.py --rank ${log_prefix}_10 > cactus_${timeout}_10.csv
