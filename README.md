# __FOREST__ :deciduous_tree::deciduous_tree::deciduous_tree:

**FO**rm **R**egular **E**xpressions **S**yn**T**hesizer 

- [Video demo](https://youtu.be/Xg8vWlHbl7Q)

- [Try the synthesizer](https://colab.research.google.com/drive/1M1fUzgJLzfZ_KrD6oR_BCi-aLLG3kXMB) on Google Colab.

- [Benchmarks descriptions](https://docs.google.com/spreadsheets/d/1NcmG0DgNYGOTuBxmWRwGORGCIvjtfbYk2sVo3RR7PyI/edit?usp=sharing).

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

## Run benchmarks:

- Using default parameters:
```
    $ python scripts/run_all.py benchmarks
```

- To view options for parameters:
```
    $ python scripts/run_all.py --help
```

## Run single instance:

- Using default parameters:

```
    $ python synth_regex.py benchmarks/cc.txt
```

- To view options for parameters:
```
    $ python synth_regex.py --help
```
