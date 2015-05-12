__author__ = 'joanna'

from bin.z3 import *

x = Int('x')
y = Int('y')
works_for = Function('works_for', IntSort(), IntSort())
s = Solver()
s.add(works_for(x) != x)
s.add(works_for(x) == y, x != y)
print s.check()
print s
print s.model()
m = s.model()
print "works_for(x) =", m.evaluate(works_for(x))
print "works_for(y) =", m.evaluate(works_for(y))