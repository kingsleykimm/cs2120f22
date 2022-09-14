from z3 import *

t = Real("t")
sq = Real("sq")
c = Real("c")

s = Solver()
s.add(t + sq +c == 10)
s.add(c+sq-t == 6)
s.add(c + t -sq == 4)

if(s.check()):
    print(s.model())
