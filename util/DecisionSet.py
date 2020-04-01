import numpy as np
import networkx as nx
import matplotlib.pyplot as plt

class DS():
    def __init__(self, K, N):
        self.K = K #The number of features.
        self.N = N #The number of nodes
        self.D = None #The number of decision nodes

        self.l = np.full(shape=(self.N+1), fill_value=False, dtype=np.bool)
        self.S = np.full(shape=(self.N+1, self.K+1), fill_value=False, dtype=np.bool) # S[i,f]: Node i discriminates on feature f
        self.t = np.full(shape=(self.N+1), fill_value=False, dtype=np.bool) # t[j] The value on node j
        self.tree = [[None] for j in range(self.N)]

    def parse_solution(self, sol): # solution = [(key, value),(key, value)....] key = (''v[1], 'v[2]', ....'v[N+1]',c'[1]'....) and other variables keys
        var_name_lookup = {"l": self.l, "S": self.S, "t": self.t}
        for var, value in sol:
            var_name = var[: var.find("[")].strip()
            var_index = var[var.find("[")+1 : var.find("]")].strip().split(",")
            assert var_name in var_name_lookup
            if var_name == "l" or var_name == "t":
                var_name_lookup[var_name][int(var_index[0])] = value
            else:

                j = int(var_index[0])
                f = int(var_index[1])
                var_name_lookup[var_name][j, f] = value



    def generate_tree(self):
        for j in range(1, self.N+1):
            value = self.t[j]
            if self.l[j]:
                feature = "class"
            else:
                feature = None
                for f in range(1, self.K+1):
                  #  print(self.S[j+1, f])
                    if self.S[j, f]:
                        feature = "f" + str(f)
                       # print('feature', feature)
                        break

            self.tree[j-1] = (feature, value)
        print('tree:', self.tree)

    def validate(self, data_features, data_classes):
        for f, c in zip(data_features, data_classes):
            pre_match = True
            pre_leaf = False
            for node in self.tree:
                node_value = node[1]
                if node[0].lower().startswith('f'):
                    node_f = int(node[0][1:])
                    if pre_leaf:
                        pre_leaf = False
                        if f[node_f - 1] == node_value:
                            pre_match = True
                        else:
                            pre_match = False
                    elif pre_match and f[node_f - 1] == node_value:
                        pass
                    else:
                        pre_match = False
                else:
                    assert node[0].lower().strip() == 'class'
                    pre_leaf = True
                    if pre_match:
                        assert c == node_value, 'Wrong solution'

    def draw(self, cnt, filename):
        nx_tree = nx.Graph()
        nx_tree_label = {}
        pos = [[0,0]]
        for j in range(1, self.N+1):
            nx_tree.add_node(j)
            if self.l[j]:
                nx_tree_label[j] = "T" if self.t[j] == 1 else "F"
            else:
                nx_tree_label[j] = self.tree[j - 1][0] if self.tree[j - 1][1] else "-{0}".format(self.tree[j - 1][0])

            if j + 1 <= self.N:
                nx_tree.add_edge(j, j+1)

            quotient = (j-1) // 10
            rem = quotient % 2
            if rem == 0:
                pos.append([j - quotient * 10, - quotient])
            else:
                pos.append([(quotient + 1) * 10 + 1 - j, -quotient])

            '''
            if j <= 10:
                pos.append([j, 0])
            elif j <= 20:
                pos.append([21-j, -1])
            elif j <= 30:
                pos.append([j - 20, -2])
            elif j <= 40:
                pos.append([41-j, -3])
            '''

        plt.figure(figsize=(8, 8))
        plt.subplot(2, 1, 1)
        nx.draw(nx_tree, pos, with_labels=True, node_color='blue')
        plt.subplot(2, 1, 2)
        nx.draw(nx_tree, pos, with_labels=True, labels=nx_tree_label, node_color='red')
        plt.savefig('trees/' + filename + '/' + str(cnt) + '.png')
        plt.close()


