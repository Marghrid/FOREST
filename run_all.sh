python -u scripts/run_tests.py -t 3600 -o -p 16 -m multitree benchmarks/ |& tee out_multitree_macf_15.txt
python -u scripts/run_tests.py -t 3600 -o -p 16 -i 5 -v 5    benchmarks/ |& tee out_5ofeach_macf_15.txt
python -u scripts/run_tests.py -t 3600 -o -p 16 -i 10 -v 10  benchmarks/ |& tee out_10ofeach_macf_15.txt
python -u scripts/run_tests.py -t 3600 -o -p 16 -m ktree     benchmarks/ |& tee out_ktree_macf_15.txt
python -u scripts/run_tests.py -t 3600 -o -p 16 -m lines     benchmarks/ |& tee out_lines_macf_15.txt
python -u scripts/run_tests.py -t 3600 -o -p 16 -m funny     benchmarks/ |& tee out_funny_macf_15.txt
python -u scripts/run_tests.py -t 3600 -o -p 16 -m nopruning benchmarks/ |& tee out_nopruning_macf_15.txt

