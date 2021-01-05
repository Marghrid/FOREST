#!/bin/bash
timeout=$1
log_prefix=${2-log_${timeout}}

if [ $# -eq 0 ]; then
    "Usage: ${0} TIMEOUT_IN_SECONDS [LOG_PREFIX]".  
    exit 1
fi

# default setting:
printf "Forest (with interaction): "
python3 scripts/make_table.py --count-not-timeout ${log_prefix}_mt

printf "Forest’s 1st regex (no interaction): "
python3 scripts/make_table.py --count-solved ${log_prefix}_mt

printf "Multi-tree w/o pruning: "
python3 scripts/make_table.py --count-not-timeout ${log_prefix}_np

printf "Dynamic-only multi-tree: "
python3 scripts/make_table.py --count-not-timeout ${log_prefix}_dy

printf "k-tree: "
python3 scripts/make_table.py --count-not-timeout ${log_prefix}_kt

printf "line-based (w/o pruning): "
python3 scripts/make_table.py --count-not-timeout ${log_prefix}_li


