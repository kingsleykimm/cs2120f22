from z3 import *

def sqrt(n) :
    sqrtn = Real('sqrtn')
    s = Solver()
    s.add(sqrtn * sqrtn == n) # replace True with required declarative spec
    isSat = s.check()
    if (isSat) :
        return s.model()
    return -1
    
    
def neg_sqrt(n) :
    neg_sqrtn = Real('sqrtn')
    s = Solver()
    s.add(And(neg_sqrtn * neg_sqrtn == n, neg_sqrtn < 0)) # replace True with required declarative spec
    isSat = s.check()
    if (isSat) :
        return s.model()
    return -1
    
print(neg_sqrt(25))