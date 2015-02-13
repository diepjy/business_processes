from bin.z3 import *
from sys import argv
# import coin

# c = argv

# real = coin('real')
# print "insert coin:", c

def returnCookie():
    print "here's your cookie!!"

def returnCoin():
    print "here's your invalid coin!!"

s = Solver()
# # coin = Bool('True')
# coinTrue = Bool('a')
# coinFalse = Bool('b')
# # If(coinTrue == True, 1, 0)
# s.push()
# s.add(coin > 0)
# print(s.check())
# s.pop()
# s.add(coin < 1)
# print(s.check())

p = Bool('p')
q = Bool('q')
r = Bool('r')
solve(Implies(p, q), r == Not(q), Or(Not(p), r))
print(s.check())
print(s.model())







