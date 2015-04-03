# import sys
# # sys.path.append('/home/joanna/Third_Year/Individual_Project/z3/bin')
from bin.z3 import *
# import z3
#from z3 import *

# print "starting Z3..."
# #(declare-const a Int)
# a = Int('a')
# #(declare-fun f (Int Bool) Int)
# f = Function('f', IntSort(), BoolSort(), IntSort())
# #(assert (> a 10))
# #(assert (< (f a true) 100))
# s = Solver()
# s.add(a > 10, f(a, True) < 100)
# #(check-sat)
# set_option(html_mode=False)
# print "checking the solver"
# print(s.check())
# print "printing the model"
# print(s.model())

x = Int('x')
y = Int('y')
s = Solver()
print s
s.add(x > 10, y == x + 2)
print s
print "Solving constraints in the solver s ..."
print s.check()
print "Create a new scope..."
s.push()
s.add(y < 11)
print s
print "Solving updated set of constraints..."
print s.check()
print "Restoring state..."
s.pop()
print s
print "Solving restored set of constraints..."
print s.check()
print s.model()