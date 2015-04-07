__author__ = 'joanna'

import ply.yacc as yacc
from Lexer import tokens

rules_used = []
tasks = []
users = []
before = []
# user pairs and task pairs should be indexes???

def p_prog(p):
	'''prog : begin
			| begin before'''

def p_begin(p):
	'''begin : TASKS COLON task_node
			 | USERS COLON user_node'''
			 # | BEFORE COLON task_node_pair'''
	if p[1] not in rules_used and p[1] == 'Tasks':
		p[0] = p[3]
		rules_used.append(p[1])
		print 'rules used tasks'
		print rules_used
	elif p[1] not in rules_used and p[1] == 'Users':
		p[0] = p[3]
		rules_used.append(p[1])
		print 'rules used users'
		print rules_used
	# elif p[1] == 'Before' and 'Tasks' in rules_used:
	# 	p[0] = p[3]
	# 	rules_used.append(p[1])
	# 	print 'rules used before'
	# 	print rules_used
	else:
		print "p error here"
		p_error(p)

def p_before(p):
	'''before : BEFORE COLON task_node_pair'''
	p[0] = p[1]

def p_task_pair(p):
	'''task_node_pair : LPAREN NODE COMMA NODE RPAREN END
				 | LPAREN NODE COMMA NODE RPAREN COMMA task_node_pair'''
	if p[2] in tasks and p[4] in tasks:
		print "tasks atm:"
		print tasks
		p[0] = [p[2]] + [p[4]]
		print(p[0])
		before.append(p[0])
		print 'before'
		print before
	else:
		p_error(p)

def p_task_node(p):
	'''task_node : NODE end
			| NODE COMMA task_node
			| NODE task_option'''
	p[0] = p[1]
	tasks.append(p[0])
	print 'tasks'
	print tasks

def p_user_node(p):
	'''user_node : NODE end
			| NODE COMMA user_node
			| NODE user_option'''
	p[0] = p[1]
	users.append(p[0])
	print "users" + users

def p_task_option(p):
	'''task_option : OPTION task_option
			  | OPTION COMMA task_node
			  | OPTION end'''
	p[0] = p[1]

def p_user_option(p):
   '''user_option : OPTION user_option
		  | OPTION COMMA user_node
		  | OPTION end'''
   p[0] = p[1]

def p_end(p):
	'''end : END
		   | END begin'''
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
    rules_used = []
    tasks = []
    users = []
    before = []