from pygments.lexer import RegexLexer, bygroups, include, words
from pygments.token import *


common_tokens = {
    'common': [
        (r'\n', Text),
        (r'\s+', Text),  # whitespaces
        (r'\\\n', Text),  # line continuations
        (r'[^\W\d]\w*', Name),
    ],
    'tla': [
        (words(("TRUE", "FALSE"), suffix=r'\b'), Name.Builtin),

        (r'(VARIABLES?|CONSTANTS?)\b', Keyword.Declaration),
        (words(("MODULE", "EXTENDS"), suffix=r'\b'), Keyword.Namespace),
        (words(("ASSUME", "ASSUMPTION", "AXIOM", "CHOOSE", "DOMAIN", "ENABLED", "EXCEPT", "IN", "INSTANCE", "LET",
                "LOCAL", "SF_", "SUBSET", "THEOREM", "UNCHANGED", "UNION", "WF_", "WITH", "IF", "THEN", "ELSE",
                "CASE", "OTHER"), suffix=r'\b'), Keyword),

        (r'(\d+)', Number.Integer),
        (r'(\d*\.\d+)', Number.Float),
        (r'((\\b|\\B)[01]+)', Number.Bin),
        (r'((\\o|\\O)[0-7]+)', Number.Oct),
        (r'((\\h|\\H)([0-9]|[a-f]|[A-F])+)', Number.Hex),

        (r'"(\\\\|\\[^\\]|[^"\\])*"', String),

        (r'(\\(lnot|neg|cap|cup|div|equiv|geq|in|intersect|leq|sqsubset|subset|subseteq|succ|succeq|supset|'
         r'supseteq|union))\b', Operator.Word),

        # (r'(\|\-\>|\\AA|\\EE)', Punctuation),  # 3 char
        (r'(\|\-\>)', Punctuation),  # 3 char
        (r'(\\AA|\\EE)', Operator),  # 3 char
        (r'(\<=\>)', Operator),  # 3 char

        # (r'(==|\\A|\\E|\<\<|\>\>)', Punctuation),  # 2 char
        (r'(\<\<|\>\>)', Punctuation),  # 2 char
        (r'(==|\\A|\\E)', Operator),  # 2 char
        (r'(\[\]|<>|!!|##|\$\$|%%|&&|=\>|\?\?|@@|\\\/|\|\||~\>)', Operator),  # 2 char
        (r'(\*\*|\+\+|\-\-|\-\||\.\.|\/\/|\/=|\/\\|:=)', Operator),  # 2 char

        (r'([\-~#$%&*+\-=\<\>\?\\\^\|\.])', Operator),  # 1 char
        (r'([\[\]\(\):{},;!\'])', Punctuation),  # 1 char
    ],
    'pluscal': [
        (r'}', Punctuation, '#pop'),
        (r'{', Punctuation, '#push'),
        
        (r'(goto)(\s+)([^\W\d]\w*)(;)', bygroups(Keyword, Text, Name.Label, Punctuation)),

        (r'variables?\b', Keyword.Declaration),
        (words(("algorithm", "define", "macro", "procedure", "process"), suffix=r'\b'), Keyword.Declaration),
        (words(("assert", "await", "begin", "call", "do", "either", "else", "elsif", "end", "goto",
                "if", "or", "print", "return", "skip", "then", "when", "while", "with"), suffix=r'\b'), Keyword),
        (r'(fair)\b', Name.Builtin),
        (r'(self)\b', Name.Builtin.Pseudo),

        (r'([^\W\d]\w*)(\s*)(:)(\s+)', bygroups(Name.Label, Text, Punctuation, Text)),
        (r'(:=|\|\|)', Punctuation),

        include('comment'),
        include('tla'),
        include('common'),
    ],
    'mpcal': [
        (words(("mpcal", "archetype", "instance", "ref"), suffix=r'\b'), Keyword.Declaration),
        (words(("mapping", "read", "write", "yield", "via"), suffix=r'\b'), Keyword),
        (r'(\$variable|\$value)\b', Name.Variable.Magic),
        include('pluscal'),
    ],
    'comment': [
        (r'\\\*.*$', Comment.Single),
        (r'\(\*', Comment.Multiline, 'multiline'),
    ],
    'multiline': [
        (r'\(\*', Comment.Multiline, '#push'),
        (r'\*\)', Comment.Multiline, '#pop'),
        (r'.|\n', Comment.Multiline),
    ]
}


class MPCalLexer(RegexLexer):
    name = 'MPCal'
    aliases = ['mpcal']
    filenames = ['*.tla']

    tokens = {
        'root': [
            include('mpcal')
        ],
        **common_tokens
    }


class TLAplusLexer(RegexLexer):
    name = 'TLA+'
    aliases = ['tla+', 'tlaplus']
    filenames = ['*.tla']

    tokens = {
        'root': [
            (r'(\-\-\-\-+)(\s*)(MODULE)(\s*)(\w*)(\s*)(\-\-\-\-+)',
                bygroups(Comment.PreProc, Text, Keyword.Namespace, Text,
                         Name, Text, Comment.PreProc)),
            (r'====+', Comment.PreProc),
            include('comment-root'),
            include('tla'),
            include('common'),
        ],
        'comment-root': [
            (r'\\\*.*$', Comment.Single),
            (r'\(\*', Comment.Multiline, 'multiline-root'),
        ],
        'multiline-root': [
            (r'(\-\-)(mpcal)(\s+)(\w+)(\s*)({)',
             bygroups(Punctuation, Keyword.Declaration, Text, Name, Text, Punctuation), 'mpcal'),
            (r'(\-\-)(algorithm|fair\s+algorithm)(\s+)(\w+)(\s*)({)',
             bygroups(Punctuation, Keyword.Declaration, Text, Name, Text, Punctuation), 'pluscal'),
            (r'\(\*', Comment.Multiline, '#push'),
            (r'\*\)', Comment.Multiline, '#pop'),
            (r'.|\n', Comment.Multiline),
        ],
        **common_tokens
    }
