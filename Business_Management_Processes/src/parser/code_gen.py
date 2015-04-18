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

while True:
    try:
        s = raw_input('busines_process > ')
    except EOFError:
        break
    if not s:
        continue
    lexer.input(s)
    # for token in lexer:
            # print(token)
    t = parser.parse(s, lexer=lexer)
    # print t

    # Collect results to SMT solver
    my_parse = MyParse()
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

    print "*********************************************"

    # Do the allocation of users and tasks if not specified
    alloc_user_task = ""
    if my_parse.allocate_users:
        # Loop through all users and allocate them to a task
        # Use BOTTOM user to verify
        user_list = my_parse.users
        task_list = my_parse.tasks

        c = []
        for i in code_gen.product(code_gen(), user_list, task_list):
            c.append(i)
        original_extra = original
        for cs in c:
            s.push()
            original_extra += "(push)\n"
            alloc_user_task = "(assert (= (alloc_user " + cs[1] + ") " + cs[0] + "))\n"
            original_extra += alloc_user_task
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

    print original_extra

    print s.check()
    m = s.model()
    print m
    m.num_sorts()
    print "sort index*********"
    print m.get_sort(0)
    z3_task_universe = m.get_universe(m.get_sort(0))
    print m.get_sort(1)
    z3_user_universe = m.get_universe(m.get_sort(1))
    print "eval *********************"
    print z3_task_universe
    print z3_user_universe
    print m.evaluate(z3_task_universe[1])
    print m.evaluate(z3_user_universe[1])
    print "-----------------------------------"
    print s.model()[z3_user_universe[0]]

    a = list()
    alloc_user_eval = ""
    alloc_user_aux = ""
    alloc_user_eval_index = -1
    alloc_user_aux_index = -1
    eval_task = []
    eval_user = []
    i = 0
    for ms in m:
        print ms
        print m[ms]
        if "Task" in str(m[ms]):
            eval_task.append(m[ms])
        if "User" in str(m[ms]):
            eval_user.append(m[ms])
        str_ms = str(ms)
        if str_ms == "alloc_user":
            alloc_user_eval = ms
            alloc_user_eval_index = i
        if "alloc_user!" in str_ms:
            alloc_user_aux = ms
            alloc_user_aux_index = i
            print alloc_user_aux
        a.append(ms)
        i += 1
    print a
    print eval_task
    print eval_user

    f1 = m[a[alloc_user_eval_index]]
    # f1_str = str(f1[0])
    print str(f1)
    print alloc_user_aux
    if str(alloc_user_aux) in str(f1):
        f2 = m[a[alloc_user_aux_index]]
        print f2
        alloc_table = []
        alloc_table = str(f2).split(",")
        print alloc_table
