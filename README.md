# Validations Synthesizer:

_Trinity Sapiens Sapiens_.
Built based on [Trinity](https://github.com/fredfeng/Trinity).

Dev Environment Setup
=====================
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
- Make an editable install with `pip`. This would automatically handles package dependencies. One of our dependencies, `z3-solver`, takes a long time to build. Please be patient.
```
    $ pip install -e ".[dev]"
    $ python setup.py sdist  # for package
```
