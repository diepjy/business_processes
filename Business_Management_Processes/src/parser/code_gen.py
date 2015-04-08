__author__ = 'joanna'

from bin.z3 import *
from Parser import *

while True:
    try:
        s = raw_input('busines_process > ')
    except EOFError:
        break
    if not s: continue
    result = parser.parse(s)
    # Collect results to SMT solver
    print "smt is in code gen" + smt

    original = smt

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
