



#Exactly one
import pycosat
import itertools

a = [1,2,3,4,5,6,7,8,9,10]
clause = []
clause.append(a)
for i in range(2, len(a)+1):
    for j in itertools.combinations(a, r=i):
        b = a.copy()
        for k in j:
            ins = b.index(k)
            b[ins] = -k
        clause.append(b)

for s in pycosat.itersolve(clause):
    print(s)
'''
a = [5,6,7,8,9,10]

print(a.index(10))



#Exactly one
import pycosat
import itertools

a = [1,2,3,4,5,6]
clause = []
clause.append(a)
b = [1,2,3]
c = -b
print(c)
'''
'''
for i in range(2, len(a)+1):
    for j in itertools.combinations(a, r=i):
        b = [1,2,3,4,5,6]
        for k in j:
            b[k-1] = -k
        clause.append(b)


for s in pycosat.itersolve(clause):
    print(s)
'''







