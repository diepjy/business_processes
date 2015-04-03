__author__ = 'joanna'

import ply.yacc as yacc
from Lexer import Lexer as lex
tokens = lex.tokens

def p_begin_tasks_rule(p):
	'''node : TASKS COLON NEW_NODE node COMMA
	        | USERS COLON NEW_NODE node COMMA'''
	print 'begin_task_rule'
	if p[1] == "Tasks":
		p[0] = ('tasks', p[4])
	elif p[1] == "Users":
		p[0] = ('users', p[4])

def p_begin_task_rule(p):
	'node : TASKS COLON'
	print "colon"
	p[0] = p[1]

# def p_begin_user_rule(p):
# 	'node : USERS COLON NEW_NODE node COMMA'
# 	print "begin user rule"
# 	p[0] = p[4]

def p_begin_before_rule(p):
	'node : BEFORE COLON NEW_NODE node_pair COMMA'
	print 'begin before rule'
	p[0] = p[4]

def p_begin_sod_rule(p):
	'node : SOD COLON NEW_NODE node_pair COMMA'
	print 'begin sod rule'
	p[0] = p[4]

def p_begin_seniority_rule(p):
	'node : SENIORITY COLON NEW_NODE node_pair COMMA'
	print 'begin seniority rule'
	p[0] = p[4]

def p_begin_bod_rule(p):
	'node : BOD COLON NEW_NODE node_pair COMMA'
	print 'begin bod rule'
	p[0] = p[4]

def p_option_node_flags(p):
	'node : NEW_NODE node option_flag'
	print 'option node flags'
	p[0] = p[2] + p[4]

def p_option_node_pair_flags(p):
	'node : NEW_NODE node_pair option_flag'
	print 'option node pair flags'
	p[0] = p[2] + p[4]

def p_option_flag(p):
	'option_flag : OPTION OPTION_FLAG'
	print 'option flag'
	p[0] = p[2]

def p_end_task_rule(p):
	'node : NEW_NODE NODE END'
	print "end task rule"
	p[0] = p[2]

def p_node_pair(p):
	'node_pair : LPAREN node COMMA node RPAREN COMMA'
	print 'node pair'
	p[0] = (p[2], p[4])

# Error rule for syntax errors
def p_error(p):
    print "Syntax error in input!"

parser = yacc.yacc()

while True:
   try:
       s = raw_input('calc > ')
   except EOFError:
       break
   if not s: continue
   result = parser.parse(s)
   print result