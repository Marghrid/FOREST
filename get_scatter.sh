#!/bin/bash
timeout=$1
log_prefix=${2-log_${timeout}}

if [ $# -eq 0 ]; then
    echo "Usage: ${0} TIMEOUT_IN_SECONDS [LOG_PREFIX]".  
    exit 1
fi


python3 scripts/make_table.py --only-synthesis-times ${log_prefix}_mt > tmp_mt.csv
python3 scripts/make_table.py --only-synthesis-times ${log_prefix}_np > tmp_np.csv
python3 scripts/make_table.py --only-synthesis-times ${log_prefix}_dy > tmp_dy.csv

echo "nopruning,dynamic,multitree" > scatter_${timeout}.csv

paste -d "," tmp_mt.csv tmp_dy.csv tmp_np.csv > scatter_${timeout}.csv
rm tmp_mt.csv tmp_dy.csv tmp_np.csv