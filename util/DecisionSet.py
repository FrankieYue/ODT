import numpy as np

class DS():
    def __init__(self, K, N):
        self.K = K #The number of features.
        self.N = N #The number of nodes
        self.D = None #The number of decision nodes

        self.l = None
        self.S = np.full(shape=(self.N+1, self.K+1), fill_value=False, dtype=np.bool) # S[i,f]: Node i discriminates on feature f
        self.t = np.full(shape=(self.N+1), fill_valule=False, dtype=np.bool) # t[j] The value on node j
