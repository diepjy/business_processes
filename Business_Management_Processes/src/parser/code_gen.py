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
or_task_list = my_parse.dict_or_task
xor_task_list = my_parse.dict_xor_task
sod_list = my_parse.dict_sod
bod_list = my_parse.dict_bod
bottom_user_execution_axiom = "(assert (forall ((t Task))" \
                              "(=> " \
                              "(executed t)" \
                              "(not(=(alloc_user t) bottom))" \
                              ")" \
                              "))\n"
not_bottom_user_execution_axiom = "(assert (forall ((t Task))" \
                                  "(=> " \
                                  "(not(executed t))" \
                                  "(=(alloc_user t) bottom)" \
                                  ")" \
                                  "))\n"

def get_task_options(d):
    smt_options = ""
    for key, value in d.iteritems():
        if value == ";":
            print "no options set"
        elif "min_sec_lv" in value:
            if "=" in value and "!=" not in value:
                # BOD
                print "= seniority"
                for t in task_list:
                    if t in value:
                        smt_options += "(assert " \
                                       "(=>" \
                                       "(and (executed " \
                                       + key + \
                                       ") (executed " \
                                       + t + \
                                       "))" \
                                       "(=(alloc_user " \
                                       + key + \
                                       ") (alloc_user " \
                                       + t + \
                                       "))" \
                                       ")" \
                                       ")\n"
            elif ">" in value:
                # More senior allocation
                print ">>>>>>> seniority"
                for t in task_list:
                    if t in value:
                        smt_options += "(assert " \
                                       "(=>" \
                                       "(and (executed " \
                                       + key + \
                                       ") (executed " \
                                       + t + \
                                       "))" \
                                       "(seniority (alloc_user " \
                                       + key + \
                                       ") (alloc_user " \
                                       + t + \
                                       "))" \
                                       ")" \
                                       ")"
            elif "<" in value:
                print "<<<<<<< seniority"
                for t in task_list:
                    if t in value:
                        smt_options += "(assert " \
                                       "(=>" \
                                       "(and (executed " \
                                       + t + \
                                       ") (executed " \
                                       + key + \
                                       "))" \
                                       "(seniority (alloc_user " \
                                       + t + \
                                       ") (alloc_user " \
                                       + key + \
                                       "))" \
                                       ")" \
                                       ")"
            elif "!=" in value:
                # SOD
                print "!!!!!!! seniority"
                for t in task_list:
                    if t in value:
                        smt_options += "(assert " \
                                       "(=>" \
                                       "(and (executed " \
                                       + key + \
                                       ") (executed " \
                                       + t + \
                                       "))" \
                                       "(not(=(alloc_user " \
                                       + key + \
                                       ") (alloc_user " \
                                       + t + \
                                       ")))" \
                                       ")" \
                                       ")\n"
        elif value == "start":
            print "START!!!!!!"
            smt_options += "(assert (forall ((t Task)) " \
                           "(before " \
                           + key + \
                           " t)" \
                           "))\n"
    print smt_options
    return smt_options

def executed_and_tasks():
    executed_tasks = ""
    print "EXE AND TASKS"
    or_xor_tasks = []
    for key, value in xor_task_list.iteritems():
        or_xor_tasks += value
    for key, value in or_task_list.iteritems():
        or_xor_tasks += value
    for p in task_list:
        if p not in or_xor_tasks:
            executed_tasks += "(assert (executed " + p + "))\n"
    print "The executed AND tasks", executed_tasks
    return executed_tasks

def executed_or_tasks():
    or_execution = ""
    for key, value in or_task_list.iteritems():
        key_list = [key]
        bracket_count = 0
        elem_count = 0
        or_execution += "(or "
        for elem in itertools.product(key_list, value):
            if elem_count < 2:
                or_execution += "(and (executed " + elem[0] + ") "
                or_execution += "(executed " + elem[1] + "))"
                bracket_count += 1
            else:
                or_execution = "(executed " + elem[1] + "))" + or_execution
                or_execution = "(and (executed " + elem[0] + ") " +or_execution
                or_execution = "(or " + or_execution
                # bracket_count += 1
                # if bracket_count % 2 == 0:
                or_execution += ")"
            elem_count += 1
        or_execution += "))\n"
    or_execution = "(assert" + or_execution
    print "OR EXECUTION RESULT", or_execution
    return or_execution

def unique_users_axiom():
    c = []
    unique_users = ""
    for i in code_gen.product(code_gen(), user_list, user_list):
        c.append(i)
    for cs in c:
        if cs[0] != cs[1]:
            s.push()
            unique_users += "(assert (not(= " + cs[0] + " " + cs[1] + ")))\n"
    print c
    return unique_users

def authorised_task_to_users_axiom(auth_list):
    auth = ""
    for key, value in auth_list.iteritems():
        auth += "(assert (or "
        for u in value:
            auth += "(=(alloc_user " + key + ")" + u +")"
        auth += "))\n"
    return auth

def executable_sod():
    sod = ""
    for p in sod_list:
        sod += "(assert (=> "
        sod += "(and (executed " + p[0] + ") (executed " + p[1] + "))"
        sod += "(not (=(alloc_user " + p[0] + ") (alloc_user " + p[1] + ")))))\n"
    return sod

def executable_bod():
    bod = ""
    for p in bod_list:
        bod += "(assert (=> "
        bod += "(and (executed " + p[0] + ") (executed " + p[1] + "))"
        bod += "(=(alloc_user " + p[0] + ") (alloc_user " + p[1] + "))))\n"
    return bod

def only_users():
    only_users = "(assert (forall ((u User)) (or"
    for u in user_list:
        only_users += "(= u " + u + ")"
    only_users += ")))\n"
    return only_users

# while True:
# try:
s = raw_input('busines_process > ')
# except EOFError:
#     break
# if not s:
#     continue
lexer.input(s)
# for token in lexer:
#         print(token)
t = parser.parse(s, lexer=lexer)
print t

# Collect results to SMT solver
original = my_parse.smt

print original

f = z3.parse_smt2_string(original)

s = z3.Solver()
import sys
if len(sys.argv) >= 2:
    s.push()
s.add(f)
print 'Result of first check', s.check()
m = s.model()
print m

auth = authorised_task_to_users_axiom(my_parse.dict_task_user_auth)

original += auth
print original
a = z3.parse_smt2_string(original)
s.add(a)
s.check()
s.model()

# go through the options and check if they are possible given the basic model
smt_options = get_task_options(my_parse.dict_tasks)
original += smt_options

print "original with options:", original
o = z3.parse_smt2_string(original)
s.add(o)
print "after options added check", s.check()
print s.model()

# Go through all combinations of seniority available
print my_parse.users
smt_seniors = original

original += only_users()
print original
o = z3.parse_smt2_string(original)
s.add(o)
print "after adding only_users axiom", s.check()
print s.model()

print "EXE SOD"
original += executable_sod()
print original
sod = z3.parse_smt2_string(original)
s.add(sod)
print "after execution sod added check", s.check()
print s.model()

print "original with options:", original
o = z3.parse_smt2_string(original)
s.add(o)
print "after options added check", s.check()
print s.model()

original += unique_users_axiom()
unique = z3.parse_smt2_string(original)
s.add(unique)
print "after options added check", s.check()
print s.model()

print "adding execution bottom axiom"
original += bottom_user_execution_axiom
original += not_bottom_user_execution_axiom
print original
bottom_user_axiom = z3.parse_smt2_string(original)
s.add(bottom_user_axiom)
print "after adding execution bottom axiom", s.check()
print s.model()

original += executed_and_tasks()
print original
exe_and_tasks = z3.parse_smt2_string(original)
s.add(exe_and_tasks)
print "after adding executed tasks in and", s.check()
print s.model()

if or_task_list:
    print "EXECUTED OR TASKS"
    original += executed_or_tasks()
    print original
    exe_or_tasks = z3.parse_smt2_string(original)
    s.add(exe_or_tasks)
    print "after adding executed tasks in or", s.check()
    print s.model()

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
        # unique_assignment = "(assert (=> (= (alloc_user " + cs[1] + ") " + cs[0] + ")"
        # bracket = ""
        # print c
        # for css in c:
        #     if css[0] != cs[0]:
        #         # print "css is ", css
        #         # print "cs is ", cs
        #         implication = "(and (not (= (alloc_user " + cs[1] + ") " + css[0] + "))"
        #         unique_assignment += implication
        #         bracket += ")"
        # print unique_assignment + bracket
        # unique_assignment += bracket + ")) \n"
        # original_extra += unique_assignment
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

print s.check()
print s.model()

#Assignment and verification
model_map_task = []
model_map_user = []
solution_map = []
Task = DeclareSort('Task')
case_bottom_user = False
for ms in m:
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
    #             # elif "User!val!0" == str(user_solution):
    #             else:
    #                 # Hit bottom user, unable to create model given existing workflow
    #                 case_bottom_user = True
    #                 break;
    #         if case_bottom_user:
    #             break;
    # if case_bottom_user:
    #     break;
if case_bottom_user:
    print "cannot assign"
    print solution_map
else:
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
    print solution_map
    print my_parse.tasks
    # # make a copy of the task list by slicing
    # checking = my_parse.tasks[:]
    # print checking
    # for solution in solution_map:
    #     print str(solution[0])
    #     if str(solution[0]) in checking:
    #         for t in checking:
    #             if t in checking:
    #                 checking.remove(t)
    # print checking
    # if checking:
    #     print "unable to assign tasks to users:", checking