__author__ = 'joanna'

from bin.z3 import *

p = Bool('p')
x = Real('x')
solve(Or(x < 5, x > 10), Or(p, x**2 == 2), Not(p))
