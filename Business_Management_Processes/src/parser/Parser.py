__author__ = 'joanna'

import ply.yacc as yacc
from Lexer import tokens

rules_used = []
tasks = []
users = []
# user pairs and task pairs should be indexes???

def p_begin(p):
	'''begin : TASKS COLON node
			 | USERS COLON node'''
	if p[1] not in rules_used and p[1] == 'Tasks':
		p[0] = p[3]
		rules_used.append(p[1])
		print rules_used
	elif p[1] not in rules_used and p[1] == 'Users':
		p[0] = p[3]
		rules_used.append(p[1])
	else:
		p_error(p)

def p_user(p):
	'begin_user : '
	if p[1] not in rules_used:
		p[0] = p[3]
		rules_used.append(p[1])
	else:
		p_error(p)

def p_task_node(p):
	'''node : NODE END
			| NODE COMMA node
			| NODE option'''
	p[0] = p[1]

def p_option(p):
	'''option : OPTION option
			  | OPTION COMMA node
			  | OPTION END'''
	p[0] = p[1]

def p_error(p):
    print "Syntax error in input!"

# Build the parser
parser = yacc.yacc()

while True:
    try:
        s = raw_input('busines_process > ')
    except EOFError:
        break
    if not s: continue
    result = parser.parse(s)


