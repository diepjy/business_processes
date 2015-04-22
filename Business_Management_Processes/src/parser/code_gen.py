__author__ = 'joanna'

from bin.z3 import *
from p_c import p_c
from lexer_class import *
from ply.lex import lex
from ply.yacc import yacc
import itertools

class MyParse(p_c):

    tokens = lexer_class.tokens

    def tokenise_input(self, input):
        self.lexer.input(input)
        for t in self.lexer:
            print t

# TODO: Tokenise file

class code_gen(object):

    def __init__(self):
        self.lexer = lex(module=lexer_class(), optimize=1)
        self.parser = yacc(module=MyParse(), start='prog', optimize=1)

    def tokenize_string(self, code):
        self.lexer.input(code)
        for token in self.lexer:
            print(token)

    def parse_string(self, code, lineno=1):
        self.lexer.lineno = lineno
        return self.parser.parse(code, lexer=self.lexer)

    def get_smt(self, code, lineno=1):
        self.lexer.lineno = lineno
        self.parser.parse(code, lexer=self.lexer)
        print 'get_smt' + MyParse.smt
        return MyParse.smt

    def product(self,*args):
        if not args:
            return iter(((),)) # yield tuple()
        return (items + (item,)
                for items in self.product(*args[:-1]) for item in args[-1])

lexer = lex(module=lexer_class(), optimize=1)
parser = yacc(module=MyParse(), start='prog', optimize=1)
my_parse = MyParse()
user_list = my_parse.users
task_list = my_parse.tasks

def get_task_options(d):
    smt_options = ""
    for key, value in d.iteritems():
        print key
        print value
        if value == ";":
            print "no options set"
        else:
            if value == "-min_sec_lv":
                smt_options += "(assert)"
    print smt_options
    return smt_options

# while True:
# try:
s = raw_input('busines_process > ')
# except EOFError:
#     break
# if not s:
#     continue
lexer.input(s)
for token in lexer:
        print(token)
t = parser.parse(s, lexer=lexer)
print t

# Collect results to SMT solver
original = my_parse.smt

print original

f = z3.parse_smt2_string(original)

s = z3.Solver ()
import sys
if len(sys.argv) >= 2:
    s.push()
s.add(f)
print 'Result of first check', s.check ()
m = s.model()
print m

print "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&"

# go through the options and check if they are possible given the basic model
get_task_options(my_parse.dict_tasks)

print "*********************************************"

# Do the allocation of users and tasks if not specified
alloc_user_task = ""
if my_parse.allocate_users:
    # Loop through all users and allocate them to a task
    # Use BOTTOM user to verify

    c = []
    for i in code_gen.product(code_gen(), user_list, task_list):
        c.append(i)
    original_extra = original
    for cs in c:
        s.push()
        original_extra += "(push)\n"
        alloc_user_task = "(assert (= (alloc_user " + cs[1] + ") " + cs[0] + "))\n"
        original_extra += alloc_user_task
        unique_assignment = "(assert (=> (= (alloc_user " + cs[1] + ") " + cs[0] + ")"
        bracket = ""
        for css in c:
            if css[0] != cs[0]:
                # print "css is ", css
                # print "cs is ", cs
                implication = "(and (not (= (alloc_user " + cs[1] + ") " + css[0] + "))"
                unique_assignment += implication
                bracket += ")"
        print unique_assignment + bracket
        unique_assignment += bracket + ")) \n"
        original_extra += unique_assignment
        # unique task allocation
        e = z3.parse_smt2_string(original_extra)
        s.add(e)
        check = s.check()
        print 'result of push', check
        if check == sat:
            m = s.model()
            print m
        elif check == unsat:
            original_extra += "(pop)\n"
            e = z3.parse_smt2_string(original_extra)
            s.pop()
            s.add(e)
            print s.check()
            print original_extra

print s.check()
m = s.model()
print m
# m.num_sorts()
# print "sort index*********"
# print m.get_sort(0)
# z3_task_universe = m.get_universe(m.get_sort(0))
# print m.get_sort(1)
# z3_user_universe = m.get_universe(m.get_sort(1))
# print "eval *********************"
# print z3_task_universe
# print z3_user_universe
# print m.evaluate(z3_task_universe[1])
# print m.evaluate(z3_user_universe[1])
print "-----------------------------------"
# print s.model()[z3_user_universe[0]]

#Assignment and verification
model_map_task = []
model_map_user = []
solution_map = []
Task = DeclareSort('Task')
case_bottom_user = False
for ms in m:
    # print ms
    # print m[ms]
    # print task_list
    # print user_list
    if str(ms) in task_list:
        model_map_task.append((ms, m[ms]))
    if str(ms) in user_list:
        model_map_user.append((ms, m[ms]))
    str_ms = str(ms)
    if str_ms == "alloc_user":
        for model_task in model_map_task:
            # print "model task is ", str(model_task[0])
            t = Const(str(model_task[0]), Task)
            user_solution = m.eval(ms(t))
            # if str(user_solution) == "User!val!0":
            #     print "cannot assign"
            #     case_bottom_user = True;
            #     break;
            for model_user in model_map_user:
                # print "str(user_solution) is ", str(user_solution)
                if str(model_user[1]) == str(user_solution):
                    # print "in model_user loop"
                    # print model_user[1]
                    # print user_solution
                    solution_map.append((t, model_user[0]))
                # elif "User!val!0" == str(user_solution):
#                 else:
#                     # Hit bottom user, unable to create model given existing workflow
#                     case_bottom_user = True
#                     break;
#             if case_bottom_user:
#                 break;
#     if case_bottom_user:
#         break;
if case_bottom_user:
    print "cannot assign"
    print solution_map
else:
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
    print solution_map