__author__ = 'joanna'

from bin.z3 import *
from p_c import p_c
from lexer_class import *
from ply.lex import lex
from ply.yacc import yacc

class MyParse(p_c):

    tokens = lexer_class.tokens

    # rules_used = []
    # tasks = []
    # users = []
    # before = []
    # seniority = []
    # sod = []
    # # user pairs and task pairs should be indexes???
    #
    # smt_sort_task = "(declare-sort Task) \n"
    # smt_sort_user = "(declare-sort User) \n"
    # smt_fun_before = "(declare-fun before (Task Task) Bool) \n"
    # smt_fun_seniority = "(declare-fun seniority (User User) Bool) \n"
    # smt_fun_sod = "(declare-fun sod (Task) User) \n"
    # smt_fun_bod = "(declare-fun bod (Task) User) \n"
    #
    # smt = ""

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

lexer = lex(module=lexer_class(), optimize=1)
parser = yacc(module=MyParse(), start='prog', optimize=1)

p = p_c()

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
    print "p_c is " + p_c().smt


    # Collect results to SMT solver
    # print "smt is in code gen" + p_c.smt
    original = MyParse.smt

    print original

    f = z3.parse_smt2_string (original)

    extra = """ """

    e = z3.parse_smt2_string (extra)

    s = z3.Solver ()
    import sys
    if len (sys.argv) >= 2: s.push ()
    s.add (f)
    s.add (e)
    print 'Result of first check', s.check ()
    m = s.model ()
    a = list ()
    for k in m:
        a.append (k() == m[k])

    for x in a: s.add (x)
    print 'Result of second check', s.check ()

    s2 = z3.Solver ()
    s2.add (f)
    s2.add (e)
    for x in a: s2.add (x)
    print 'Independent result', s2.check ()
