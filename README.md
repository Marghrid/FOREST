# __FOREST__ 
:deciduous_tree::deciduous_tree::deciduous_tree::deciduous_tree::deciduous_tree:
**FO**rm **R**egular **E**xpressions **S**yn**T**hesizer 
:deciduous_tree::deciduous_tree::deciduous_tree::deciduous_tree::deciduous_tree:

- [Try the synthesizer](https://colab.research.google.com/drive/1M1fUzgJLzfZ_KrD6oR_BCi-aLLG3kXMB) on Google Colab.

- [Benchmarks descriptions](https://docs.google.com/spreadsheets/d/1NcmG0DgNYGOTuBxmWRwGORGCIvjtfbYk2sVo3RR7PyI/edit?usp=sharing).

- Based on [Trinity](https://github.com/fredfeng/Trinity).

## Dev Environment Setup
- Prerequisite:
    - python 3.6+  
- It is preferable to have a dedicated virtualenv for this project:
```
    $ git clone <this repo>
    $ cd Validations-Synthesizer
    $ mkdir venv
    $ python3 -m venv venv
    $ source venv/bin/activate
```
- Make an editable install with `pip`. This automatically handles package dependencies. One of the dependencies, `z3-solver`, takes a long time to build. Please be patient.
```
    $ pip install -e ".[dev]"
    $ python setup.py sdist  # for package
```
