from bin.z3 import *

x, y = Ints('x y')

s = Solver()
s.add(x - y > 2, x > 3, y < 4)
print s.check()
m = s.model()
print m
# We can retrieve the value assigned to x by using m[x].
# The api has a function called substitute that replaces (and simplifies)
# an expression using a substitution.
# The substitution is a sequence of pairs of the form (f, t).
#  That is, Z3 will replace f with the term t.

F1 = x - y < 2

# Let us use substitute to replace x with 10
print substitute(F1, (x, IntVal(10)))

# Now, let us replace x and y with values assigned by the model m.
print substitute(F1, (x, m[x]), (y, m[y]))