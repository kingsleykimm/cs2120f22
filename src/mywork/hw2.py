#Kingsley Kim, id: bjb3az
from z3 import *
def hw2():
    X = Bool('X')
    Y = Bool('Y')
    Z = Bool('Z')
    s = Solver()
    #C1: X ∨ Y, X ⊢ ¬Y: 
    # If X or Y is true and X is true, then Y must be false
    # Not valid, since X and Y can both be true and X ∨ Y is still true 
    C1 = (Implies(And(Or(X,Y), X), Not(Y)))
    s.add(Not(C1))
    #not valid
    if(s.check() == unsat):
        print("C1 is valid")
    else:
        print("C1 isn't valid, here's a counterexample: ", s.model())
    #Why C1 isn't valid, English translation: 
    # If it is true that a car can have 4 seats or 2 seats, and we know that some cars have 
    # 4 seats (X), which is true, this doesn't entail that other cars can't have 2 seats (¬Y).
    s.reset()
    
    
    
    #C2: X, Y ⊢ X ∧ Y:
    # If X, Y is true, this entails that X and Y is true
    #Valid 
    Y = True
    C2 = Implies(X, And(X, Y))
    s.add(Not(C2))
    if(s.check() == unsat):
        print("C2 is valid")
    else:
        print("C2 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    Y = Bool('Y')
    #C3: X ∧ Y ⊢ X
    # If X and Y is true, this entails X must be true
    #Valid
    C3 = (Implies(And(X, Y), X))
    s.add(Not(C3))
    if(s.check() == unsat):
        print("C3 is valid")
    else:
        print("Here's a counterexample: ", s.model())
    s.reset()
    
    #C4: X ∧ Y ⊢ Y, 
    #And elimination right rule, if X and Y is true, this entails that Y is also true
    #Valid
    C4 = (Implies(And(X, Y), X))
    s.add(Not(C4))
    if(s.check() == unsat):
        print("C4 is valid")
    else:
        print("Here's a counterexample: ", s.model())
    s.reset()
    
    #C5: ¬¬X ⊢ X
    #Negation rule: When the negation of the negation of x is true, it translates to X being true
    #Valid
    C5 = (Implies(Not(Not(X)), X))
    s.add(Not(C5))
    if(s.check() == unsat):
        print("C5 is valid")
    else:
        print("Here's a counterexample: ", s.model())
    s.reset()
    
    #C6: ¬(X ∧ ¬X) 
    #no contradiction rule: If X is true, then the negation of the conjuction of X and not X must be true
    #Valid, since the conjuction will always return false, and the negation will then return true
    C6 = Not(And(X, Not(X)))
    s.add(Not(C6))
    if(s.check() == unsat):
        print("C6 is valid")
    else:
        print("Here's a counterexample: ", s.model())
    s.reset()
    
    #C7: X ⊢ X ∨ Y
    # If X is true, then X or Y will always be true
    #Valid, since or only needs one argument to be true to be true
    C7 = Implies(X, Or(X, Y))
    s.add(Not(C7))
    if(s.check() == unsat):
        print("C7 is valid")
    else:
        print("Here's a counterexample: ", s.model())
    s.reset()
    
    #C8: Y ⊢ X ∨ Y
    #If Y is true, then X or Y will always be true
    #Valid, since Or only needs one argument to be true, and Y is true
    C8 = Implies(Y, Or(X, Y))
    s.add(Not(C8))
    if(s.check() == unsat):
        print("C8 is valid")
    else:
        print("Here's a counterexample: ", s.model())
    s.reset()
    
    #C9: X → Y, ¬X ⊢ ¬ Y 
    # If X implies Y, then the negation of X will be the same as the negation of Y
    # Not valid, since X could be false and Y could be true and implies would still be true, but the latter statement would be false
    C9 = Implies(And(Implies(X, Y), Not(X)), Not(Y))
    #English counterexample: Say that if there are grey clouds (X), it implies it will rain later in the day (Y).
    # If we also know that the negation is true, that there will be no grey clouds today (¬X), it could still rain
    #later in the day, meaning that Y would be false and this proposition is not valid.
    s.add(Not(C9))
    if(s.check() == unsat):
        print("C9 is valid")
    else:
        print("C9 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    
    #C10: X → Y, Y → X ⊢ X ↔ Y
    # If X implies Y, and Y implies X, then X and Y 
    #Valid
    C10 = Implies(And(Implies(X, Y), Implies(Y, X)), X == Y)
    s.add(Not(C10))
    if(s.check() == unsat):
        print("C10 is valid")
    else:
        print("C10 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C11: X ↔ Y ⊢ X → Y
    # If X is true iff Y is true, this means that X implies Y
    # Valid, since the only two cases are when X and Y are both true or false, and both these cases return true when X implies Y
    C11 = Implies(X == Y, Implies(X, Y))
    s.add(Not(C11))
    if(s.check() == unsat):
        print("C11 is valid")
    else:
        print("C11 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C12: X ↔ Y ⊢ Y → X
    # If X is true iff Y is true, then Y implies X
    # Valid, since just like C11, there are only two cases: when Y and X are both true 
    C12 = Implies(X == Y, Implies(Y, X))
    s.add(Not(C12))
    if(s.check() == unsat):
        print("C12 is valid")
    else:
        print("C12 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C13: X ∨ Y, X → Z, Y → Z ⊢ Z
    # If X or Y is true, X implies Z, and Y implies Z, then Z must be true
    # Valid
    C13 = Implies(And(Or(X, Y), Implies(X, Z), Implies(Y, Z)), Z)
    s.add(Not(C13))
    if(s.check() == unsat):
        print("C13 is valid")
    else:
        print("C13 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C14: X → Y, Y ⊢ X
    # If X implies Y, and Y is true, this entails X will be true
    #not valid, case where X = False and Y = True still returns true for X -> Y, but X won't be true
    C14 = Implies(And(Implies(X, Y), Y), X)
    #English counterexample: Say that the clouds being grey is condition X and rain today is condition Y,
    # so the clouds being grey implies it will rain today, which is true. Say Y is True, that it rained today,
    # but X is false, that there was no grey clouds, that the sky was sunny, which can happen.  
    s.add(Not(C14))
    if(s.check() == unsat):
        print("C14 is valid")
    else:
        print("C14 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C15: X → Y, X ⊢ Y 
    # If X implies Y, and X is true, this entails that Y must be true
    # Valid
    C15 = Implies(And(Implies(X, Y), X), Y)
    s.add(Not(C15))
    if(s.check() == unsat):
        print("C15 is valid")
    else:
        print("C15 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C16: X → Y, Y → Z ⊢ X → Z
    #If X implies Y, and Y implies Z, this entails that X will imply Z through transistivity
    # Valid
    C16 = Implies(And(Implies(X, Y), Implies(Y, Z)), Implies(X, Z))
    s.add(Not(C16))
    if(s.check() == unsat):
        print("C16 is valid")
    else:
        print("C16 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C17: X → Y ⊢ Y → X
    # If X implies Y, this entails that Y implies X
    #Not  valid
    C17 = Implies(Implies(X, Y), Implies(Y, X))
    s.add(Not(C17))
    if(s.check() == unsat):
        print("C17 is valid")
    else:
        print("C17 isn't valid, here's a counterexample: ", s.model())
    #English counterexample: Being able to drive a car implies that you are over 18, but being over 
    #18 does not imply that you can drive a car.
    s.reset()
    
    
    #C18: X → Y ⊢ ¬Y → ¬X
    # If X implies Y, this entails that the negation of Y implies the negation of X
    # valid
    C18 = Implies(Implies(X, Y), Implies(Not(Y), Not(X)))
    s.add(Not(C18))
    if(s.check() == unsat):
        print("C18 is valid")
    else:
        print("C18 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C19: ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
    # Iff the negation of X or Y is true, then the conjuction of not X and not Y is true
    # Valid 
    C19 = (Not(Or(X, Y)) == And(Not(X), Not(Y)))
    s.add(Not(C19))
    if(s.check() == unsat):
        print("C19 is valid")
    else:
        print("C19 isn't valid, here's a counterexample: ", s.model())
    s.reset()
    
    #C20: ¬(X ∧ Y) ↔ ¬X ∨ ¬Y
    # Iff the negation of X and Y is true, then the disjunction of not X and not Y is true
    #Valid 
    C20 = (Not(And(X, Y)) == Or(Not(X), Not(Y)))
    s.add(Not(C20))
    if(s.check() == unsat):
        print("C20 is valid")
    else:
        print("C20 isn't valid, here's a counterexample: ", s.model())
    s.reset()
hw2()