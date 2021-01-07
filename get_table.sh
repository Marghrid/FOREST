#!/bin/bash
log_prefix=${1-log}

# default setting:
printf "Forest (with interaction): "
python3 scripts/make_table.py --count-not-timeout-all ${log_prefix}_mt

printf "Forest’s 1st regex (no interaction): "
python3 scripts/make_table.py --count-solved-all ${log_prefix}_mt

printf "Multi-tree w/o pruning: "
python3 scripts/make_table.py --count-not-timeout-all ${log_prefix}_np

printf "Dynamic-only multi-tree: "
python3 scripts/make_table.py --count-not-timeout-all ${log_prefix}_dy

printf "k-tree: "
python3 scripts/make_table.py --count-not-timeout-all ${log_prefix}_kt

printf "line-based (w/o pruning): "
python3 scripts/make_table.py --count-not-timeout-all ${log_prefix}_li

printf "Regel: "
python scripts/make_table.py -r ${log_prefix}_rg  --regel-count-not-timeout-all ${log_prefix}_mt 2>/dev/null

printf "Regel PBE: "
python scripts/make_table.py -r ${log_prefix}_rgp --regel-count-not-timeout-all ${log_prefix}_mt 
