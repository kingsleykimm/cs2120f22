from z3 import *

c = Bool('c')
d = Bool('d')
e = Bool('e')
h = Bool('h')
m = Bool('m')
#true = guilty, false = innocent
#need to find a satisfiable solution, or a true result
s = Solver()
s.add(Or(c, d, e, h, m))
s.add(Implies(And(c, Not(h)), d))
s.add(Implies(Not(c), Not(m)))
s.add(Implies(h, m))
s.add(Not(And(c, h))) #Chase and Heath are not both guilty
s.add(Implies(Not(h), Not(d))) #Unless Heath is guilty, Derek is innocent

if(s.check()):
    print(s.model())