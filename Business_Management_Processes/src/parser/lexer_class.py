__author__ = 'joanna'

class lexer_class(object):
    # Handle reserved words
    reserved = {
        'Tasks' : 'TASKS',
        'Users' : 'USERS',
        'Before' : 'BEFORE',
        'SoD' : 'SOD',
        'Seniority' : 'SENIORITY',
        'BoD' : 'BOD',
        'users' : 'USERS_OPTION',
        'allocate' : 'ALLOCATE',
        'min_sec_lv' : 'MIN_SEC_LV',
        'start' : 'START',
        'Or' : 'OR',
        'Xor' : 'XOR',
        'Execution' : 'EXECUTION',
        'Alloc' : 'ALLOC',
        'Authorised' : 'AUTHORISED'
    }

    # List of token names
    tokens = [
        'COLON',
        'NODE',
        'OPTION',
        'COMMA',
        'LPAREN',
        'RPAREN',
        'END',
        'EQ',
        'GEQ',
        'LEQ',
        'NEQ',
        'LSQPAREN',
        'RSQPAREN'
    ] + list(reserved.values())

    # Regular expression rules for simple tokens
    t_COLON = r':'
    t_NODE = r'(%s|%s)' % (r'"(\\"|[^"])*"', r"'(\\'|[^'])*'")
    # t_OPTION = r'-[a-zA-Z_][a-zA-Z0-9_]*'
    t_OPTION = r'-'
    t_COMMA = r','
    t_LPAREN = r'\('
    t_RPAREN = r'\)'
    t_END = r';'
    t_EQ = r'='
    t_GEQ = r'>'
    t_LEQ = r'<'
    t_NEQ = r'!='
    t_LSQPAREN = r'\['
    t_RSQPAREN = r'\]'

    # Check for reserved words
    def t_ID(self, t):
        r'[a-zA-Z_][a-zA-Z_0-9]*'
        t.type = self.reserved.get(t.value,'ID')
        return t

    # Define a rule so we can track line numbers
    def t_newline(self,t):
        r'\n+'
        t.lexer.lineno += len(t.value)

    # Error handling rule
    def t_error(self,t):
        # print "Illegal character '%s'" % t.value[0]
        t.lexer.skip(1)