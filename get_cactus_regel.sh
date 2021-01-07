#!/bin/bash
log_prefix=${1-log}

# REGEL
python3 scripts/make_table.py --rank-regel -r ${log_prefix}_rg  ${log_prefix}_mt > cactus_3600_rg.csv

# REGEL PBE
python3 scripts/make_table.py --rank-regel -r ${log_prefix}_rgp  ${log_prefix}_mt > cactus_3600_rgp.csv

