from setuptools import setup, find_packages

install_dependencies = [
    'Click',
    'z3-solver',
    'termcolor'
]
develop_dependencies = [
    'mypy',  # for type checking
    'lark-parser',  # for parsing
    'sphinx',  # for documentation generation
]
setup(
    name='Validations Synthesizer',
    version='0.1dev',
    packages=find_packages(),
    license='LICENSE.txt',
    description='User input validatios synthesis tool',
    install_requires=install_dependencies,
    extras_require={
        'dev': develop_dependencies
    },
    entry_points={
        'console_scripts': [
            'parse-tyrell-spec=tyrell.parse_tyrell_spec:cli',
        ],
    },
)
