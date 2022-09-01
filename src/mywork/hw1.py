#Kingsley Kim, ID: bjb3az
from z3 import *
from itertools import combinations
#25 literals, 5 booleans

def at_most_one(squares): #checks there's at most one true, or queen in the given squares
    c = []

    for pair in combinations(squares, 2):
        a, b = pair[0], pair[1]
        c += [Or(Not(a), Not(b))]
    return And(c) #does a conjuction on all the disjunctions in the list


#Create literals in square
x = [[Bool("x_%i_%i" % (i, j)) for j in range(5)] for i in range(5)] #square is created

s = Solver()

for i in range(5):
    s.add(Or(x[i])) #makes sure at least one true or queen is in a row, only time it returns false is when there isn't a queen
for i in range(5): #at most one queen per row
    col = []
    for j in range(5):
        col += [x[j][i]]
    s.add(at_most_one(col)) #adds constraints of one queen per column
    s.add(at_most_one(x[i])) #one queen per row constraints

for i in range(4):
    diag_1 = []
    diag_2 = []
    diag_3 = []
    diag_4 = []
    for j in range(5 - i):
        diag_1 += [x[i+j][j]]
        diag_2 += [x[i+j][4-j]]
        diag_3 += [x[4-(i+j)][j]]
        diag_4 += [x[4- (i+j)][4-j] ]
    s.add(at_most_one(diag_1))
    s.add(at_most_one(diag_2))
    s.add(at_most_one(diag_3))
    s.add(at_most_one(diag_4))
print(s.check())
    
m = s.model()
for i in range(5):
    line = ""
    for j in range(5):
        if m.evaluate(x[i][j]):
            line += "x "
        else:
            line += ". "
    print(line)

