__author__ = 'joanna'

from bin.z3 import *

x = Bool('x')
y = Bool('y')
works_for = Function('works_for', BoolSort(), BoolSort())
s = Solver()
s.add(works_for(works_for(x)) == False)
s.add(works_for(x) == True, x != y)
print s.check()
m = s.model()
print "works_for(works_for(x)) =", m.evaluate(works_for(works_for(x)))
print "works_for(x) =", m.evaluate(works_for(x))