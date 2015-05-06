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
    print d
    for key, value in d.iteritems():
        print "key", key
        print "value", value
        if value == ";":
            print "no options set"
        elif "min_sec_lv" in value:
            if "=" in value and "!=" not in value:
                print "= seniority"
                print "value is ", value
                for t in task_list:
                    if t in value:
                        print "t is in ", t
                        smt_options += "(assert (forall ((u5 User) (u4 User) (u3 User) (u6 User)) " \
                                       "(=> " \
                                       "(and (and (and (and (and (and (and (and (and (seniority u3 u4) (seniority u5 u4)) (seniority u6 u3)) (seniority u6 u5)) (not(= u3 u5))) (not(= u3 u4))) (not(= u3 u6))) (not(= u4 u5))) (not(= u4 u6)))(not(= u5 u6))) " \
                                       "(and (or (=(alloc_user " \
                                       + key + \
                                       ") u3) (=(alloc_user " \
                                       + key + \
                                       ") u5)) (or (=(alloc_user " \
                                       + t + \
                                       ") u3) (=(alloc_user " \
                                       + t + \
                                       ") u5)))" \
                                       ")" \
                                       "))"
            elif ">" in value:
                # More senior allocation
                print ">>>>>>> seniority"
                for t in task_list:
                    if t in value:
                        print "t is in ", t
                        smt_options += "(assert (forall ((u1 User) (u2 User) (u3 User))" \
                                       "(=> " \
                                       "(and" \
                                       "(and (seniority u2 u3) (not(= u2 u3)))" \
                                       "(not(= u3 u2)))" \
                                       "(and (=(alloc_user " \
                                       + key + \
                                       ") u2) (=(alloc_user " \
                                       + t + \
                                       ") u3))" \
                                       ")" \
                                       "))\n"
            elif "<" in value:
                print "<<<<<<< seniority"
                for t in task_list:
                    if t in value:
                        print "t is in ", t
                        smt_options += "(assert (forall ((u1 User) (u2 User) (u3 User))" \
                                       "(=> " \
                                       "(and" \
                                       "(and (seniority u2 u3) (not(= u2 u3)))" \
                                       "(not(= u3 u2)))" \
                                       "(and (=(alloc_user " \
                                       + key + \
                                       ") u3) (=(alloc_user " \
                                       + t + \
                                       ") u2))" \
                                       ")" \
                                       "))\n"
            elif "!=" in value:
                # Just OR together the > and < axioms
                print "!!!!!!! seniority"
                for t in task_list:
                    if t in value:
                        print "t is in ", t
                        smt_options += "(assert (forall ((u1 User) (u2 User) (u3 User))" \
                                       "(or" \
                                       "(=> " \
                                       "(and" \
                                       "(and (seniority u2 u3) (not(= u2 u3)))" \
                                       "(not(= u3 u2)))" \
                                       "(and (=(alloc_user t3) u3) (=(alloc_user t4) u2))" \
                                       ")" \
                                       "(=> " \
                                       "(and" \
                                       "(and (seniority u2 u3) (not(= u2 u3)))" \
                                       "(not(= u3 u2)))" \
                                       "(and (=(alloc_user t3) u2) (=(alloc_user t4) u3))" \
                                       ")" \
                                       ")" \
                                       "))\n"
        elif value == "start":
            print "START!!!!!!"
            smt_options += "(assert (forall ((t Task)) " \
                           "(before " \
                           + key + \
                           " t)" \
                           "))\n"
        elif value == "execution":
            print "EXECUTION!!!!!!!!!!"
            if "or" in value:
                print "OR EXE!!!!!!!!!"
                for t in task_list:
                    if t in value:
                        print t
                        # smt_options += "(assert (=>(before " \
                        #                + key + " " + t  \
                        #                ")" \
                        #                "(alloc_user)" \
                        #                "))"
            elif "and" in value:
                print "AND EXE!!!!!!!!!!!"
    print smt_options
    return smt_options

# def unique_users_axiom():
#     unique_users = "(assert (forall ((u1 User) (u2 User))" \
#                    "(=> (not(= u1 u2)) (not(= u2 u1)))" \
#                    "))\n"
#     print unique_users
#     return unique_users

def unique_users_axiom():
    print my_parse.users
    c = []
    unique_users = ""
    for i in code_gen.product(code_gen(), user_list, user_list):
        c.append(i)
    print c
    for cs in c:
        if cs[0] != cs[1]:
            s.push()
            # original += "(push)\n"
            unique_users += "(assert (not(= " + cs[0] + " " + cs[1] + ")))\n"
            # sn = z3.parse_smt2_string(original)
            # s.add(sn)
            # if s.check() == unsat:
            #     original += "(pop)\n"
            #     s.pop()
    print c
    return unique_users

def authorised_task_to_users_axiom(auth_list):
    print auth_list
    auth = ""
    for key, value in auth_list.iteritems():
        print "key", key
        print "value", value
        auth += "(assert (or "
        for u in value:
            print u
            auth += "(=(alloc_user " + key + ")" + u +")"
        auth += "))\n"
    print auth
    return auth

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

print "code gen dict task user auth", my_parse.dict_task_user_auth

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

print "!!!!!!! user_alloc_dict", my_parse.dict_user_alloc

auth = authorised_task_to_users_axiom(my_parse.dict_task_user_auth)

original += auth

print original
a = z3.parse_smt2_string(original)
s.add(a)
s.check()
s.model()

print "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&"

# go through the options and check if they are possible given the basic model
smt_options = get_task_options(my_parse.dict_tasks)
# print original + smt_options
original += smt_options

print "original with options:", original
o = z3.parse_smt2_string(original)
s.add(o)
print "after options added check", s.check()
print s.model()

# Go through all combinations of seniority available
print my_parse.users
smt_seniors = original
# c = []
# for i in code_gen.product(code_gen(), user_list, user_list):
#     c.append(i)
# print c
# for cs in c:
#     if cs[0] != cs[1]:
#         s.push()
#         original += "(push)\n"
#         original += "(assert (not(seniority " + cs[0] + " " + cs[1] + ")))\n"
#         sn = z3.parse_smt2_string(original)
#         s.add(sn)
#         if s.check() == unsat:
#             original += "(pop)\n"
#             s.pop()
# print c

print "original with options:", original
o = z3.parse_smt2_string(original)
s.add(o)
print "after options added check", s.check()
print s.model()

print "*********************************************"

original += unique_users_axiom()
unique = z3.parse_smt2_string(original)
s.add(unique)
print "after options added check", s.check()
print s.model()

print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"

# Do the allocation of users and tasks if not specified
alloc_user_task = ""
if my_parse.allocate_users:
    # Loop through all users and allocate them to a task
    # Use BOTTOM user to verify

    c = []
    for i in code_gen.product(code_gen(), user_list, task_list):
        c.append(i)
    original_extra = original
    print c
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