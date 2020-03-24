import numpy as np
import networkx as nx
from networkx.drawing.nx_agraph import write_dot, graphviz_layout
import matplotlib.pyplot as plt

class DT(): # For adjust a solution

    def __init__(self, K, N): #Some basic parameters for a DT
        self.K = K # K: The number of features.
        self.N = N # N: The number of nodes.
        self.LR = lambda i: set(filter((lambda jj: jj % 2 == 0), [j for j in range(i + 1, min(2 * i, N - 1) + 1)]))
        self.RR = lambda i: set(filter((lambda jj: jj % 2 == 1), [j for j in range(i + 2, min(2 * i + 1, N) + 1)]))
        self.v = np.full(shape=(N+1), fill_value=False, dtype=np.bool ) # v[i] == 1 iff node i is a leaf node, i = 1...N
        self.l = np.full(shape=(N+1,N+1), fill_value=False, dtype=np.bool ) # l[i,j] == 1 iff node i has node j as the left child
        self.r = np.full(shape=(N+1,N+1), fill_value=False, dtype=np.bool ) # r[i,j] == 1 iff node i has node j as the right child
        self.a = np.full(shape=(K+1,N+1), fill_value=False, dtype=np.bool ) # a[r,j] == 1 iff feature fr is assigned to node j
        self.c = np.full(shape=(N+1), fill_value=False, dtype=np.bool ) # c[j] == 1 iff class of leaf node j is 1

    def parse_DT(self, parent=1):
        leftChild = []
        for j in self.LR(parent):
            if self.l[parent,j] == True:
                leftChild.append(j)
        rightChild = []
        for j in self.RR(parent):
            if self.r[parent,j] == True:
                rightChild.append(j)
        assert (len(leftChild) == 1 and len(rightChild) == 1) or (len(leftChild) == 0 and len(rightChild) == 0)
        if len(leftChild) == 0 and len(rightChild) == 0:
            return (parent,(),()), ('1' if self.c[parent] == 1 else '0',(),())
        elif len(leftChild) == 1 and len(rightChild) == 1:
            childLeftInfo = self.parse_DT(leftChild[0])
            childRightInfo = self.parse_DT(rightChild[0])
            return (parent, childLeftInfo[0], childRightInfo[0]), (np.argmax(self.a[:,parent]), childLeftInfo[1], childRightInfo[1])
        else:
            raise Exception("Error")

    def print_DT(self):
        tree, assign = self.parse_DT()
        print(tree, assign)

    def print_vars(self): #Print variables indices where values are true
        print("v")
        print(np.argwhere(self.v == 1))

        print("l")
        print(np.argwhere(self.l == 1))

        print("r")
        print(np.argwhere(self.r == 1))

        print("a")
        print(np.argwhere(self.a == 1))

        print("c")
        print(np.argwhere(self.c == 1))

    #Update the DT variables using a solution
    def parse_solution(self, sol): # solution = [(key, value),(key, value)....] key = (''v[1], 'v[2]', ....'v[N+1]',c'[1]'....) and other variables keys
        var_name_lookup = {"v": self.v, "l": self.l, "r": self.r, "a": self.a, "c": self.c}
        for var, value in sol:
            var_name = var[1: var.find("[")].strip() #var[0] is ','
            var_index = var[var.find("[")+1 : var.find("]")].strip(",")
            assert var_name in var_name_lookup
            if var_name == "v" or var_name == "c":
                var_name_lookup[var_name][int(var_index)] = value
            else:
                i = int(var_index.split(',')[0])
                j = int(var_index.split(',')[1])
                var_name_lookup[var_name][i, j] = value

    def validate(self, data_features, data_classes): # Validate if all examples data classified correctly. Ensure the accuracy for examples is 100%
        for x, y in zip(data_features, data_classes):
            curr_node = 1
            found = False
            while not found:
                feature_index = np.argmax(self.a[:, curr_node]) # The feature index in the current node
                data_feature_index = feature_index - 1 # The feature index in example data

                if x[data_feature_index] == 0:
                    next_node = [j for j in self.LR(curr_node) if self.l[curr_node, j] == 1]
                else:
                    next_node = [j for j in self.RR(curr_node) if self.r[curr_node, j] == 1]
               # print(next_node)
                assert len(next_node) == 1
                next_node = next_node[0]
                has_feature = [self.a[r, next_node] for r in range(1, self.K+1)]
                if sum(has_feature) == 0:
                    if y == 1:
                        assert self.c[next_node] == True
                    else:
                        assert self.c[next_node] == False
                    found = True
                curr_node = next_node

    def draw(self, cnt, filename):
        tree, ass = self.parse_DT()
        nx_tree = nx.Graph()
        nx_tree_label = {}

        def extract_info(tree, ass):
            c, l, r = tree
            c_a, c_l, c_r = ass

            nx_tree.add_node(c)

            if l == ():
                assert r == ()
                nx_tree_label[c] = 'T' if c_a == '1' else 'F'
            else:
                assert r != ()
                nx_tree_label[c] = c_a
                nx_tree.add_edge(c, l[0])
                nx_tree.add_edge(c, r[0])
                extract_info(l, c_l)
                extract_info(r, c_r)
        extract_info(tree, ass)


     #   nx.nx_agraph.write_dot(nx_tree, 'test.dot')
     #   pos = graphviz_layout(nx_tree, prog='dot')

        pos = [(0,0) for i in range(self.N + 1)]
        def extract_depth(tree, node_index=1, depth=0):
            c, l, r = tree
            pos[node_index] = (0, -abs(depth))
            if l != ():
                assert r != ()
                for j in range(node_index+ 1, min(2 *  node_index, self.N - 1) + 1):
                    if self.l[node_index, j]:
                        l_c_index = j
                        r_c_index = j + 1
                        break
                extract_depth(l, l_c_index, depth+1)
                extract_depth(r, r_c_index, depth+1)



        def extract_width(node_index=1, depth=None):
            if depth == None:
                depth = abs(pos[self.N][1])
            child_distance = (2 ** (depth - 1) + 2 ** (depth) - 1) / 10

            if not self.v[node_index]:
                for j in range(node_index+ 1, min(2 *  node_index, self.N - 1) + 1):
                    if self.l[node_index, j]:
                        l_c_index = j
                        r_c_index = j + 1
                        break

                pos[l_c_index] = (pos[node_index][0] - child_distance / 2, pos[l_c_index][1])
                pos[r_c_index] = (pos[node_index][0] + child_distance / 2, pos[r_c_index][1])

                if not self.v[l_c_index]:
                    extract_width(l_c_index, depth - 1)
                if not self.v[r_c_index]:
                    extract_width(r_c_index, depth - 1)

                '''
                if self.v[l_c_index] and self.v[r_c_index]:
                    pos[l_c_index] = (pos[node_index][0] - child_distance / 2, pos[l_c_index][1])
                    pos[r_c_index] = (pos[node_index][0] + child_distance / 2, pos[r_c_index][1])

                if not self.v[l_c_index] and self.v[r_c_index]:
                    pos[l_c_index] = (pos[node_index][0] - child_distance / 2, pos[l_c_index][1])
                    pos[r_c_index] = (pos[node_index][0], pos[r_c_index][1])
                    extract_width(l_c_index, depth - 1)

                if self.v[l_c_index] and not self.v[r_c_index]:
                    pos[l_c_index] = (pos[node_index][0], pos[l_c_index][1])
                    pos[r_c_index] = (pos[node_index][0] + child_distance / 2, pos[r_c_index][1])
                    extract_width(r_c_index, depth - 1)
                '''

        extract_depth(tree)
        extract_width()
        print(pos)


       # pos = [(0,0), (0,0),(-1,-1), (1,-1),(-2,-2),(-1, -2), (1, -2), (3,-2), (-3,-3), (-1,-3)]

        plt.figure(figsize=(6, 10))
        plt.subplot(2, 1, 1)
        nx.draw(nx_tree, pos, with_labels=True, node_color='blue')
        plt.subplot(2, 1, 2)
      #  pos = graphviz_layout(nx_tree, prog='dot')
        nx.draw(nx_tree, pos, with_labels=True, labels=nx_tree_label, node_color='red')
        plt.savefig('trees/' + filename + '/' + str(cnt) + '.png')
        plt.close()



    def cal_lnode(self):
        tree, ass = self.parse_DT()

        def extract_lnode(tree):
            c, l, r = tree
            if l == ():
                assert r == ()
                return 1
            else:
                assert r != ()
                return extract_lnode(l) + extract_lnode(r)

        num_lnode = extract_lnode(tree)
        return num_lnode

    def cal_depth(self):
        tree, ass = self.parse_DT()

        def extract_depth(tree):
            c, l, r = tree
            if l == ():
                assert r == ()
                return 0
            else:
                assert r != ()
                return max(extract_depth(l), extract_depth(r)) + 1
        depth = extract_depth(tree)
        return depth