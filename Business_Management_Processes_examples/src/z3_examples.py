# import sys
# # sys.path.append('/home/joanna/Third_Year/Individual_Project/z3/bin')
from bin.z3 import *
# import z3
#from z3 import *

#(echo "starting Z3...")
#(declare-const a Int)
a = Int('a') 
#(declare-fun f (Int Bool) Int)
f = Function('f', IntSort(), BoolSort(), IntSort())
#(assert (> a 10))
#(assert (< (f a true) 100))
s = Solver()
s.add(a > 10, f(a, True) < 100)
#(check-sat)
print(s.check())
print(s.model())