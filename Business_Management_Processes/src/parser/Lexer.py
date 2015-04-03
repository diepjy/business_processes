__author__ = 'joanna'

import ply.lex as lex

class Lexer:
    # Handle reserved words
    reserved = {
        'Tasks' : 'TASKS',
        'Users' : 'USERS',
        'Before' : 'BEFORE',
        'SoD' : 'SOD',
		'Seniority' : 'SENIORITY',
		'BoD' : 'BOD'
    }

    # List of token names
    tokens = [
        'COLON',
        'NODE',
        'OPTION',
        'OPTION_FLAG',
        'NEW_NODE',
        'COMMA',
        'LPAREN',
        'RPAREN',
		'END'
    ] + list(reserved.values())

    # Regular expression rules for simple tokens
    t_COLON = r':'
    t_NODE = r'(%s|%s)' % (r'"(\\"|[^"])*"', r"'(\\'|[^'])*'")
    t_OPTION = r'-[a-zA-Z_][a-zA-Z0-9_]*'
    t_NEW_NODE = r'\t'
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

    def t_OPTION_FLAG(self, t):
        r'\d+'
        return t

    # Define a rule so we can track line numbers
    def t_newline(self,t):
        r'\n+'
        t.lexer.lineno += len(t.value)

    # Error handling rule
    def t_error(self, t):
        print "Illegal character '%s'" % t.value[0]
        t.lexer.skip(1)

    # Build the lexer
    def build(self,**kwargs):
        self.lexer = lex.lex(module=self, **kwargs)

    # Test it output
    def test(self,data):
        self.lexer.input(data)
        while True:
             tok = self.lexer.token()
             if not tok: break
             print tok

	# Parsing rules
	precedence = ()

	def p_task_pair(self, p):
		'task_pair : LPAREN task COMMA task RPAREN'
		p[0] = (p[2], p[4])

	def p_user_task_pair(self, p):
		'user_task_pair : LPAREN task COMMA task RPAREN'
		p[0] = (p[2], p[4])

# Build the lexer and try it out
m = Lexer()
m.build()           # Build the lexer
data = '''Tasks:
	'purchaseApproved' -before;
Users:
'''
m.test(data)     # Test it

