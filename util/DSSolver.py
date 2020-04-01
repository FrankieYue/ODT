import numpy as np
#from pysmt.shortcuts import *
from pysmt.oracles import get_logic
import pycosat
import itertools

class DSSolver():
    def __init__(self, K, N, data):
        self.K = K  # The number of features.
        self.N = N  # The number of nodes
        self.D = None  # The number of decision nodes
        self.I = len(data[0])

        self.var_l = np.empty(shape=(self.N+1), dtype=object) #var_l[j] == 1 if node j is a leaf node
        self.var_v = np.empty(shape=(self.I+1, self.N+1), dtype=object) # var_v[i,j] is one when item i is valid in node j
        self.var_S = np.empty(shape=(self.N+1, self.K+1), dtype=object) #var_S[j,f]: Node j discriminates on feature f
        self.var_t = np.empty(shape=(self.N+1), dtype=object)  # var_t[j] The value on node j
        self.sig = np.empty(shape=(self.K+1, self.I+1), dtype=object) # The value of feature f in item i
        self.c = np.empty(shape=(self.I+1), dtype=object) # The class values of items
        self.var_d0 = np.empty(shape=(self.K+1, self.N+1), dtype=object)
        self.var_d1 = np.empty(shape=(self.K+1, self.N+1), dtype=object)
        self.var_vd = np.empty(shape=(self.I + 1, self.N + 1), dtype=object)
        self.var_vl = np.empty(shape=(self.I + 1, self.N + 1), dtype=object)
        self.clause = []

        self.var2ids = {}
        self.ids2var = {}
        self.cnf_ids = 0
        self.all_var_sol = None

        self.basic_keys = ("l", "S", "t")  # DS variables
        self.all_basic_vars = set()  # All basic DS variables With indices
        self.all_vars = set() # All variables with indices

        for f in range(1, self.sig.shape[0]):
            for i in range(1, self.sig.shape[1]):
                self.sig[f, i] = data[0][i-1][f-1]

        for i in range(1, self.c.shape[0]):
            self.c[i] = data[1][i-1]

   #     def add_key(var_with_index, var_name):
    #        if var_name in self.basic_keys:
     #           self.all_basic_vars.add(var_with_index)
      #      self.all_vars.add(var_with_index)

        def add_vars_1d(vars, var_name):
            for i in range(1, vars.shape[0]):
                vars[i] = var_name + "[" + str(i) + "]"
           #     add_key(vars[i], var_name)

        def add_vars_2d(vars, var_name):
            for i in range(1, vars.shape[0]):
                for j in range(1, vars.shape[1]):
                    vars[i, j] = var_name + "[" + str(i) + "," + str(j) + "]"
                    #add_key(vars[i, j], var_name)

        add_vars_1d(self.var_l, "l")
        add_vars_2d(self.var_v, "v")
        add_vars_2d(self.var_S, "S")
        add_vars_1d(self.var_t, "t")
        add_vars_2d(self.var_d0, "d0")
        add_vars_2d(self.var_d1, "d1")
        add_vars_2d(self.var_vd, "vd")
        add_vars_2d(self.var_vl, "vl")

    def get_cnf_id(self, var, value=1):
        if var not in self.var2ids:
            self.cnf_ids += 1
            self.var2ids[var] = self.cnf_ids

            assert self.cnf_ids not in self.ids2var
            self.ids2var[self.cnf_ids] = var

        return self.var2ids[var] if value == 1 else -self.var2ids[var]

    def encode_constraints(self):  # Encode the constraints in paper
        def cons_1(self):  # All data are valid at the first node
            for i in range(1, self.I + 1):
                cnf_id = [self.get_cnf_id(self.var_v[i, 1])]
                self.clause.append(cnf_id)


        def cons_2(self):
            for j in range(1, self.N+1):
                for f in range(1, self.K+1):
                    #a
                    f1 = []
                    f1.append(self.get_cnf_id(self.var_d0[f, j], '-'))
                    f1.append(self.get_cnf_id(self.var_S[j, f]))
                    self.clause.append(f1)

                    f2 = []
                    f2.append(self.get_cnf_id(self.var_d0[f, j], '-'))
                    f2.append(self.get_cnf_id(self.var_t[j], '-'))
                    self.clause.append(f2)

                    f3 = []
                    f3.append(self.get_cnf_id(self.var_d0[f, j]))
                    f3.append(self.get_cnf_id(self.var_S[j, f], '-'))
                    f3.append(self.get_cnf_id(self.var_t[j]))
                    self.clause.append(f3)

                    #b
                    f1 = []
                    f1.append(self.get_cnf_id(self.var_d1[f, j], '-'))
                    f1.append(self.get_cnf_id(self.var_S[j, f]))
                    self.clause.append(f1)

                    f2 = []
                    f2.append(self.get_cnf_id(self.var_d1[f, j], '-'))
                    f2.append(self.get_cnf_id(self.var_t[j]))
                    self.clause.append(f2)

                    f3 = []
                    f3.append(self.get_cnf_id(self.var_d1[f, j]))
                    f3.append(self.get_cnf_id(self.var_S[j, f], '-'))
                    f3.append(self.get_cnf_id(self.var_t[j], '-'))
                    self.clause.append(f3)

                    '''
                    aaa = [self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in f1]
                    bbb = [self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in f2]
                    ccc = [self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in f3]
                    print(aaa, bbb, ccc)
                    '''

        def cons_3(self): #vd[ij] <-> v[ij] /\ exists d0/1[fj]
            for i in range(1, self.I+1):
                for j in range(1, self.N+1):
                    f1 = []
                    f1.append(self.get_cnf_id(self.var_vd[i, j], "-"))
                    f1.append(self.get_cnf_id(self.var_v[i, j]))
                    self.clause.append(f1)

                    f2 = []
                    f2.append(self.get_cnf_id(self.var_vd[i, j], "-"))

                    f3 = []
                    f3.append(self.get_cnf_id(self.var_vd[i, j]))
                    f3.append(self.get_cnf_id(self.var_v[i, j], "-"))
                    for f in range(1, self.K+1):
                        if self.sig[f, i] == 0:
                            f2.append(self.get_cnf_id(self.var_d0[f, j]))

                            ff = f3.copy()
                            ff.append(self.get_cnf_id(self.var_d0[f, j], "-"))
                            self.clause.append(ff)
                        else:
                            assert self.sig[f, i] == 1
                            f2.append(self.get_cnf_id(self.var_d1[f, j]))

                            ff = f3.copy()
                            ff.append(self.get_cnf_id(self.var_d1[f, j], "-"))
                            self.clause.append(ff)
                        #abc.append([self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in ff])

                    self.clause.append(f2)
                    '''
                    aaa = [self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in f1]
                    bbb = [self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in f2]
                 #   ccc = [self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in f3]
                    print(aaa, bbb, abc,'\n')
                    '''


        def cons_4(self): #v[i,j+1] <-> l[j] \/ vd[ij]
            for i in range(1, self.I+1):
                for j in range(1, self.N):
                    f1 = []
                    f1.append(self.get_cnf_id(self.var_v[i, j+1], "-"))
                    f1.append(self.get_cnf_id(self.var_l[j]))
                    f1.append(self.get_cnf_id(self.var_vd[i, j]))
                    self.clause.append(f1)

                    f2 = []
                    f2.append(self.get_cnf_id(self.var_v[i, j + 1]))
                    f2.append(self.get_cnf_id(self.var_l[j], "-"))
                    self.clause.append(f2)

                    f3 = []
                    f3.append(self.get_cnf_id(self.var_v[i, j + 1]))
                    f3.append(self.get_cnf_id(self.var_vd[i, j], "-"))
                    self.clause.append(f3)

        def cons_5(self): # Exactly one S[j1] + S[j2]... + S[jf] + l[j]
            def cons_5a(self):  # l[j] <-> forall f in F -S[jf]
                for j in range(1, self.N + 1):
                    f2 = []
                    f2.append(self.get_cnf_id(self.var_l[j]))
                    for f in range(1, self.K + 1):
                        f1 = []
                        f1.append(self.get_cnf_id(self.var_l[j], "-"))
                        f1.append(self.get_cnf_id(self.var_S[j, f], "-"))
                        self.clause.append(f1)

                        f2.append(self.get_cnf_id(self.var_S[j, f]))
                    self.clause.append(f2)

            def cons_5b(self): # Exactly one S[j1] \/ l[j] S[j2]... \/ l[j] S[jf] \/ l[j]

                for j in range(1, self.N + 1):
                    or_f = []
                    f1 = []
                    f1.append(self.get_cnf_id(self.var_l[j]))

                    for f in range(1, self.K+1):
                        or_f.append(self.get_cnf_id(self.var_S[j, f]))
                        f1.append(self.get_cnf_id(self.var_S[j, f]))

                    self.clause.append(f1)
                   # aaa = [self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in or_f ]
                 #   print('\nj:', j, aaa)

                    for a in range(len(or_f)):
                        for b in range(a+1, len(or_f)):
                            new_f = []
                            new_f.append(self.get_cnf_id(self.var_l[j]))
                            new_f.append(-or_f[a])
                            new_f.append(-or_f[b])
                            self.clause.append(new_f)

                    ''' Old method (Expensive)
                    for a in range(2, len(or_f) + 1):
                        for b in itertools.combinations(or_f, r=a):
                            new_f = or_f.copy()
                            for c in b:
                                ids = new_f.index(c)
                                new_f[ids] = -c
                            new_f.append(self.get_cnf_id(self.var_l[j])) # For first or literal
                            self.clause.append(new_f)
                            bbb = [self.ids2var[abs(jj)] if jj > 0 else '-' + self.ids2var[abs(jj)] for jj in new_f ]
                         #   print('a:', a, 'j:', j, bbb)
                     '''
            cons_5a(self)
            cons_5b(self)

        def cons_6(self): # S[j+1,f] -> l[j] \/ exists S[j,f']
            for j in range(1, self.N):
                for f in range(1, self.K+1):
                    formulas = []
                    formulas.append(self.get_cnf_id(self.var_S[j+1, f], "-"))
                    formulas.append(self.get_cnf_id(self.var_l[j]))
                    for ff in range(1, f):
                        formulas.append(self.get_cnf_id(self.var_S[j, ff]))

                    self.clause.append(formulas)

        def cons_7(self): #vl[i,j] <-> l[j] /\ v[ij]
            for i in range(1, self.I+1):
                for j in range(1, self.N+1):
                    f1 = []
                    f1.append(self.get_cnf_id(self.var_vl[i, j], "-"))
                    f1.append(self.get_cnf_id(self.var_l[j]))
                    self.clause.append(f1)

                    f2 = []
                    f2.append(self.get_cnf_id(self.var_vl[i, j], "-"))
                    f2.append(self.get_cnf_id(self.var_v[i, j]))
                    self.clause.append(f2)

                    f3 = []
                    f3.append(self.get_cnf_id(self.var_vl[i, j]))
                    f3.append(self.get_cnf_id(self.var_l[j], "-"))
                    f3.append(self.get_cnf_id(self.var_v[i, j], "-"))
                    self.clause.append(f3)

        def cons_8(self): #Exists vl[ij]
            for i in range(1, self.I+1):
                or_f = []
                for j in range(1, self.N+1):
                    or_f.append(self.get_cnf_id(self.var_vl[i, j]))
                self.clause.append(or_f)


        def cons_9(self): #11 vl[ij] -> c[i] == t[j]
            for i in range(1, self.I+1):
                for j in range(2, self.N+1):
                    formulas = []
                    formulas.append(self.get_cnf_id(self.var_vl[i, j], "-"))
                    if self.c[i]:
                        formulas.append(self.get_cnf_id(self.var_t[j]))
                    else:
                        formulas.append(self.get_cnf_id(self.var_t[j], "-"))

                    self.clause.append(formulas)

        def cons_10(self):
            formulas = []
            formulas.append(self.get_cnf_id(self.var_l[1], "-"))
            self.clause.append(formulas)

        def cons_11(self):
            for j in range(1, self.N):
                f1 = []
                f1.append(self.get_cnf_id(self.var_l[j + 1], '-'))
                f1.append(self.get_cnf_id(self.var_l[j]))
                self.clause.append(f1)

                f2 = []
                f2.append(self.get_cnf_id(self.var_l[j + 1]))
                f2.append(self.get_cnf_id(self.var_l[j], '-'))
                self.clause.append(f2)




        #cons_0(self)
        cons_1(self)
        cons_2(self)
        cons_3(self)
        cons_4(self)
        cons_5(self) # Problem constraint 5b
        cons_6(self)
        cons_7(self)
        cons_8(self)
        cons_9(self)
        cons_10(self)
      #  cons_11(self)




    def solve(self):
        self.encode_constraints()
        s = pycosat.solve(self.clause)
        self.all_var_sol =[]
        ds_var_sol = []
        aaa = []
        if s == "UNSAT":
           # print("There is no solutions for node number {0} ".format(self.N))
            return None
        else:
            for ids in s:
                aaa.append(ids)
                var_name = self.ids2var[abs(ids)]
                var_val = 1 if ids > 0 else 0
                self.all_var_sol.append((var_name, var_val))
                if var_name[0] in self.basic_keys:
                    ds_var_sol.append((var_name, var_val))
           # sol = [('S[1,1]', 1).....]
           # print(self.all_var_sol)
    
          #  print("sol:\n",ds_var_sol)
            return ds_var_sol
     #   print('aaa', aaa[0]==-1),








