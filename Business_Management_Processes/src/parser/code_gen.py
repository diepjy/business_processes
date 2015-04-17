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
#     original = '''
# (declare-sort Task)
# (declare-const t1 Task)
# (declare-const t2 Task)
# (declare-sort User)
# (declare-fun alloc (User Task) Bool)
# (declare-fun alloc_user (Task) User)
# (declare-const u1 User)
# (assert (not (= (alloc_user t1) (alloc_user t2))))
# (push)
# (assert (= (alloc_user t2) u1))
# (push)
# (assert (= (alloc_user t1) u1))
# (pop)
# (check-sat)
# '''
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
    print s.model()