# __FOREST__ :deciduous_tree::deciduous_tree::deciduous_tree:

**FO**rm **R**egular **E**xpressions **S**yn**T**hesizer 

- [Video demo](https://youtu.be/Xg8vWlHbl7Q).

- [Try the synthesizer](https://colab.research.google.com/drive/1M1fUzgJLzfZ_KrD6oR_BCi-aLLG3kXMB) on Google Colab.

- Based on [Trinity](https://github.com/fredfeng/Trinity).

## Dev Environment Setup

- Prerequisite:
  - python 3.7+
  
- Python packages dependencies:
  - click
  - termcolor
  - z3-solver
  
- It is preferable to have a dedicated virtual environment for this project:
```
    $ git clone <this repo>
    $ cd FOREST
    $ mkdir venv
    $ python3 -m venv venv
    $ source venv/bin/activate
```

- Install dependencies in virtual environment:
```
    $ pip install click termcolor z3-solver
```

## Run single instance:

- Using default parameters:

```
    $ python forest.py benchmarks/cc.txt
```

- To view options for parameters:
```
    $ python forest.py --help
```

## Run benchmarks:

- Using default parameters:
```
    $ python scripts/run_benchmarks.py benchmarks
```

- To view options for parameters:
```
    $ python scripts/run_benchmarks.py --help
```

## Run a new instance:

If you wish to create a new instance, you have to provide FOREST a set of valid examples and a set of invalid examples. If you wish to synthesize capture conditions, you need to provide a set of conditional invalid examples as well. Additionally, you can provide a ground truth, which is a correct answer for this instance, written as a regex that can be interpreted using [Python's regex library](https://docs.python.org/3/library/re.html).

You can write the example strings on a file formatted as follows:

- Comments. Any text before the valid examples is ignored;
- A line containing only "++" (without quotes);
- Valid example strings, one string per line;
- A line containing only "--" (without quotes);
- Invalid example strings, one string per line;
- \[OPTIONAL\] A line containing only "+-" (without quotes);
- \[OPTIONAL\] Conditional invalid example strings, one string per line;
- \[OPTIONAL\] A line containing only "\*\*" (without quotes);
- \[OPTIONAL\] Ground truth, a Python interpretable regex;

The following is an example of a FOREST instance file:

```
Dates example:
++
19/08/1996
26/10/1998
22/09/2000
01/12/2001
29/09/2003
31/08/2015
--
19/08/96
26-10-1998
22.09.2000
1/12/2001
29/9/2003
2015/08/31
+-
32/08/1996
26/13/1998
22/00/2000
00/12/2001
09/22/2003
**
([0-9][0-9])/([0-9][0-9])/[0-9][0-9], $0 <= 31, $0 >= 1, $1 <= 12, $1 >= 1
```

