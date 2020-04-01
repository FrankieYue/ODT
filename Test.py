


'''
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


import networkx as nx
import matplotlib.pyplot as plt


def draw(N=11, cnt=1):
    nx_tree = nx.Graph()
    nx_tree_label = {}
    pos = [[0, 0]]
    for j in range(1, N+1):
        nx_tree.add_node(j)

        if j + 1 <= N:
            nx_tree.add_edge(j, j + 1)
        pos.append([j, 0])
    nx_tree_label[1] = "-A"
    nx_tree_label[2] = "B"
    nx_tree_label[3] = "-C"
    nx_tree_label[4] = "1"
    nx_tree_label[5] = "C"
    nx_tree_label[6] = "0"
    nx_tree_label[7] = "-B"
    nx_tree_label[8] = "C"
    nx_tree_label[9] = "1"
    nx_tree_label[10] = "-C"
    nx_tree_label[11] = "0"

    plt.figure(figsize=(10, 2))
    plt.subplot(2, 1, 1)
    nx.draw(nx_tree, pos, with_labels=True, node_color='blue')
    plt.subplot(2, 1, 2)
    nx.draw(nx_tree, pos, with_labels=True, labels=nx_tree_label, node_color='red')
    plt.savefig('trees/' + str(cnt) + '.png')
    plt.close()

draw()

def draw2(N=12, cnt=2):
    nx_tree = nx.Graph()
    nx_tree_label = {}
    pos = [[0, 0]]
    for j in range(1, N+1):
        nx_tree.add_node(j)

        if j + 1 <= N:
            nx_tree.add_edge(j, j + 1)
        pos.append([j, 0])

    nx_tree_label[1] = "B"
    nx_tree_label[2] = "-C"
    nx_tree_label[3] = "1"
    nx_tree_label[4] = "B"
    nx_tree_label[5] = "C"
    nx_tree_label[6] = "0"
    nx_tree_label[7] = "-B"
    nx_tree_label[8] = "-C"
    nx_tree_label[9] = "0"
    nx_tree_label[10] = "-B"
    nx_tree_label[11] = "C"
    nx_tree_label[12] = "1"

    plt.figure(figsize=(10, 2))
    plt.subplot(2, 1, 1)
    nx.draw(nx_tree, pos, with_labels=True, node_color='blue')
    plt.subplot(2, 1, 2)
    nx.draw(nx_tree, pos, with_labels=True, labels=nx_tree_label, node_color='red')
    plt.savefig('trees/' + str(cnt) + '.png')
    plt.close()

draw2()
'''
#Exactly one
import pycosat

a = [1,2,3,4,5,6]
clause = []
clause.append(a)

for i in range(len(a)):
    for j in range(i+1, len(a)):
        clause.append([-a[i], -a[j]])

for s in pycosat.itersolve(clause):
    print(s)





