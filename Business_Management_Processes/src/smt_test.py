__author__ = 'joanna'

from bin.z3 import *

s = Solver()

Tasks = DeclareSort('Tasks')
Users = DeclareSort('Users')

t1 = Const('t1', Tasks)
t2 = Const('t2', Tasks)
u1 = Const('u1', Users)
bottom = Const('bottom', Users)

alloc_user = Function('alloc_user', Tasks, Users)

s.push()
s.add(ForAll([t1], alloc_user(t1) != bottom))
s.push()
s.add(alloc_user(t1) != alloc_user(t2))

print s.check()
print s.model()
print s.model().eval(alloc_user(t1))


