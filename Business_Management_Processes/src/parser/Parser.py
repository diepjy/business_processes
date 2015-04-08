__author__ = 'joanna'

import ply.yacc as yacc
from Lexer import tokens

rules_used = []
tasks = []
users = []
before = []
seniority = []
sod = []
# user pairs and task pairs should be indexes???

smt_sort_task = "(declare-sort Task) \n"
smt_sort_user = "(declare-sort User) \n"
smt_fun_before = "(declare-fun before (Task Task) Bool) \n"
smt_fun_seniority = "(declare-fun seniority (User User) Bool) \n"
smt_fun_sod = "(declare-fun sod (Task) User) \n"
smt_fun_bod = "(declare-fun bod (Task) User) \n"

smt = ""

# TODO: option flags

def p_prog(p):
	'''prog : begin
			| begin rules'''

def p_begin(p):
    '''begin : TASKS COLON task_node
			 | USERS COLON user_node'''
    global smt
    if p[1] not in rules_used and p[1] == 'Tasks':
        p[0] = p[3]
        rules_used.append(p[1])
        smt = smt_sort_task + smt
    elif p[1] not in rules_used and p[1] == 'Users':
        p[0] = p[3]
        smt = smt_sort_user + smt
    else:
        print "p error here"
        p_error(p)

def p_rules(p):
    '''rules : BEFORE COLON task_node_pair
             | SENIORITY COLON user_node_pair
             | SOD COLON task_node_pair
             | BOD COLON task_node_pair'''
    p[0] = p[3]

def p_task_pair(p):
    '''task_node_pair : LPAREN NODE COMMA NODE RPAREN END
                 | LPAREN NODE COMMA NODE RPAREN COMMA task_node_pair'''
    if p[2] in tasks and p[4] in tasks:
        p[0] = [p[2]] + [p[4]]
        print(p[0])
        before.append(p[0])
    else:
        p_error(p)

def p_user_pair(p):
    '''user_node_pair : LPAREN NODE COMMA NODE RPAREN END
                      | LPAREN NODE COMMA NODE RPAREN COMMA user_node_pair'''
    if p[2] in users and p[4] in users:
        p[0] = [p[2]] + [p[4]]
        seniority.append(p[0])
    else:
        p_error(p)

def p_task_node(p):
    '''task_node : NODE end
            | NODE COMMA task_node
            | NODE task_option'''
    p[0] = p[1]
    tasks.append(p[0])
    global smt
    smt = "(declare-const " + p[0] + " Tasks)\n" + smt

def p_user_node(p):
    '''user_node : NODE end
            | NODE COMMA user_node
            | NODE user_option'''
    p[0] = p[1]
    users.append(p[0])
    print "users"
    print users
    global smt
    smt = "(declare-const " + p[0] + " Users) \n" + smt

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

print "smt in parser: " + smt

# while True:
#     try:
#         s = raw_input('busines_process > ')
#     except EOFError:
#         break
#     if not s: continue
#     result = parser.parse(s)
#     # Collect results to SMT solver
#     print "smt is " + smt
#     rules_used = []
#     tasks = []
#     users = []
#     before = []