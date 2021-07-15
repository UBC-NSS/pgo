from setuptools import setup, find_packages

setup(
    name='mpcallexer',
    packages=find_packages(),
    entry_points=
    """
    [pygments.lexers]
    tlapluslexer = mpcallexer.lexer:TLAplusLexer
    mpcallexer = mpcallexer.lexer:MPCalLexer
    """,
)
