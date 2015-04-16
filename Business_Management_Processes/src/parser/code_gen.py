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
    if not s: continue
    lexer.input(s)
    for token in lexer:
            print(token)
    t = parser.parse(s, lexer=lexer)
    print t

    # Collect results to SMT solver
    # print "smt is in code gen" + p_c.smt
    my_parse = MyParse()
    # original = MyParse.smt
    original = my_parse.smt
    print original

#     original = """
# (declare-sort Task)
# (declare-const approve Task)
# (declare-const send Task)
# (declare-sort User)
# (declare-const alice User)
# (declare-const bob User)
# (declare-fun alloc_user (Task) User)
# (assert (not(= (alloc_user approve) (alloc_user send))))
#  """

    f = z3.parse_smt2_string(original)

    # e = z3.parse_smt2_string (extra)

    s = z3.Solver ()
    import sys
    if len(sys.argv) >= 2:
        s.push()
    s.add(f)
    # s.add (e)
    print 'Result of first check', s.check ()
    m = s.model()
    print m

    # Do the allocation of users and tasks if not specified
    alloc_user_task = ""
    if my_parse.allocate_users:
        print 'push'
        s.push()
        print my_parse.users
        # Loop through all users and allocate them to a task
        # Use BOTTOM user to verify
        user_list = my_parse.users
        task_list = my_parse.tasks
        print task_list
        for u in user_list:
            u.translate(None, '!@#$\'u')
            print u
            alloc_user_task += "(assert (alloc (" + ")))"
        print user_list
        print task_list

        print 'carteasian product'
        c = []
        f = []
        for i in code_gen.product(code_gen(), user_list, task_list):
            print i
            c.append(i)
        print c

    # Parse output into readable
    a = list ()
    # for k in m:
    #     a.append (k() == m[k])
    #
    # for x in a: s.add (x)
    # print 'Result of second check', s.check ()
    #
    # s2 = z3.Solver ()
    # s2.add (f)
    # # s2.add (e)
    # for x in a: s2.add (x)
    # print 'Independent result', s2.check ()

