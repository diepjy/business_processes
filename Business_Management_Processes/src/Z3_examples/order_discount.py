__author__ = 'joanna'

from bin.z3 import *

def dis(x):
    n = Int('n')
    s = Int('s')
    sol = Solver()

    sol.add(n == x)
    print n
    sol.push()
    sol.add(n > 100, s == 10 * n)
    if sol.check() == unsat:
        print("n <= 100 orders")
        sol.pop()
        sol.push()
        sol.add(n <= 100, s == 20 * n)
    else:
        print("n > 100 orders")
    sol.check()
    m = sol.model()
    d = m[s]
    dis = d.as_long()
    sol.push()
    sol.add(s > 2000)
    if sol.check() == unsat:
        sol.pop()
        sol.push()
        sol.add(s >= 1000, s <= 2000)
        if sol.check() == unsat:
            print("no discount")
            sol.pop()
        else:
            dis *= 0.9
            print("10% discount")
    else:
        dis *= 0.8
        print("20% discount")
    print sol
    print sol.check()
    print("with discount " + str(dis))

dis(300)