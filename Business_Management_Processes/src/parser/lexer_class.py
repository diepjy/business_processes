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
        'allocate' : 'ALLOCATE'
    }

    # List of token names
    tokens = [
        'COLON',
        'NODE',
        'OPTION',
        'COMMA',
        'LPAREN',
        'RPAREN',
        'END'
    ] + list(reserved.values())

    # Regular expression rules for simple tokens
    t_COLON = r':'
    t_NODE = r'(%s|%s)' % (r'"(\\"|[^"])*"', r"'(\\'|[^'])*'")
    t_OPTION = r'-[a-zA-Z_][a-zA-Z0-9_]*'
    # t_OPTION = r'-'
    t_COMMA = r','
    t_LPAREN = r'\('
    t_RPAREN = r'\)'
    t_END = r';'

    # Check for reserved words
    def t_ID(self, t):
        r'[a-zA-Z_][a-zA-Z_0-9]*'
        t.type = self.reserved.get(t.value,'ID')
        return t

    # List of tasks
    tasks = {}

    # List of Users
    users = {}

    # Define a rule so we can track line numbers
    def t_newline(self,t):
        r'\n+'
        t.lexer.lineno += len(t.value)

    # Error handling rule
    def t_error(self,t):
        # print "Illegal character '%s'" % t.value[0]
        t.lexer.skip(1)