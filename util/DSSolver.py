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
        self.data_features = data[0]
        self.data_class = data[1]
        self.I = len(self.data_features)

        self.var_l = np.empty(shape=(self.N+1), dtype=object) #var_l[j] == 1 if node j is a leaf node
        self.var_v = np.empty(shape=(self.I+1, self.N+1), dtype=object) # var_v[i,j] is one when item i is valid in node j
        self.var_S = np.empty(shape=(self.N+1, self.K+1), dtype=object) #var_S[j,f]: Node j discriminates on feature f
        self.var_t = np.empty(shape=(self.N+1), dtype=object)  # var_t[j] The value on node j
        self.sig = np.empty(shape=(self.K+1, self.I+1), dtype=object) # The value of feature f in item i
        self.var_d0 = np.empty(shape=(self.K+1, self.N+1), dtype=object)
        self.var_d1 = np.empty(shape=(self.K+1, self.N+1), dtype=object)
        self.var_p = np.empty(shape=(self.I + 1, self.N + 1), dtype=object)
        self.clause = []

        self.var2ids = {}
        self.ids2var = {}
        self.cnf_ids = 0



        '''
        pysmt
        self.formulas = None
        self.solver = None
        self.num_sol = 0
        '''
        
        
        
        self.basic_keys = ("l", "S", "t")  # DS variables
        self.all_basic_vars = set()  # All basic DS variables With indices
        self.all_vars = set() # All variables with indices

        for f in range(1, self.sig.shape[0]):
            for i in range(1, self.sig.shape[1]):
                self.sig[f, i] = self.data_features[i-1][f-1]

        def add_key(var_with_index, var_name):
            if var_name in self.basic_keys:
                self.all_basic_vars.add(var_with_index)
            self.all_vars.add(var_with_index)

        def add_vars_1d(vars, var_name):
            for i in range(1, vars.shape[0]):
                vars[i] = var_name + "[" + str(i) + "]"
                add_key(vars[i], var_name)

        def add_vars_2d(vars, var_name):
            for i in range(1, vars.shape[0]):
                for j in range(1, vars.shape[1]):
                    vars[i, j] = var_name + "[" + str(i) + "," + str(j) + "]"
                    add_key(vars[i, j], var_name)

        add_vars_1d(self.var_l, "l")
        add_vars_2d(self.var_v, "v")
        add_vars_2d(self.var_S, "S")
        add_vars_1d(self.var_t, "t")
        add_vars_2d(self.var_d0, "d0")
        add_vars_2d(self.var_d1, "d1")
        add_vars_2d(self.var_p, "p")

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
            for j in range(1, self.N):
                for f in range(1, self.K+1):
                    # d0[f,j] = S[jf] /\ -t[j]
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

        def cons_3(self):
            for j in range(1, self.N):
                for f in range(1, self.K+1):
                    # d1[f,j] = S[jf] /\ t[j]
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

        def cons_4(self): # -l[j] /\ u[ij] <-> Exist f in F, d(0/1)[fj]
            for i in range(1, self.I+1):
                for j in range(1, self.N):
                    or_formulas = []
                    for f in range(1, self.K+1):
                        if self.sig[f,i] == 1:
                            or_formulas.append(self.get_cnf_id(self.var_d1[f, j]))
                        else:
                            or_formulas.append(self.get_cnf_id(self.var_d0[f, j]))

                    f1 = or_formulas
                    f1.append(self.get_cnf_id(self.var_l[j]))
                    f1.append(self.get_cnf_id(self.var_v[i, j], '-'))
                    self.clause.append(f1)

                    f_l = [self.get_cnf_id(self.var_l[j], '-')]
                    f_v = [self.get_cnf_id(self.var_v[i, j])]
                    for f in range(1, self.K+1):
                        or_f = f_l
                        or_v = f_v
                        if self.sig[f,i] == 1:
                            oo_f = self.get_cnf_id((self.var_d1[f, j]), '-')
                        else:
                            oo_f = self.get_cnf_id((self.var_d1[f, j]), '-')
                        or_f.append(oo_f)
                        or_v.append(oo_f)
                        self.clause.append(or_f)
                        self.clause.append(or_v)

        def cons_5(self): # p[ij] <-> -l[j] /\ v[ij]
            for i in range(1, self.I+1):
                for j in range(1, self.N):
                    f1 = []
                    f1.append(self.get_cnf_id(self.var_p[i,j], '-'))
                    f1.append(self.get_cnf_id(self.var_l[j], '-'))
                    self.clause.append(f1)

                    f2 = []
                    f2.append(self.get_cnf_id(self.var_p[i, j], '-'))
                    f2.append(self.get_cnf_id(self.var_v[i, j]))
                    self.clause.append(f2)

                    f3 = []
                    f3.append(self.get_cnf_id(self.var_p[i, j]))
                    f3.append(self.get_cnf_id(self.var_l[j]))
                    f3.append(self.get_cnf_id(self.var_v[i, j], '-'))
                    self.clause.append(f3)

        def cons_6(self): # v[i,j+1] <-> l[j] \/ p[ij]
            for i in range(1, self.I + 1):
                for j in range(1, self.N):
                    f1 = []
                    f1.append(self.get_cnf_id(self.var_v[i, j+1], '-'))
                    f1.append(self.get_cnf_id(self.var_l[j]))
                    self.clause.append(f1)

                    f2 = []
                    f2.append(self.get_cnf_id(self.var_v[i, j+1], '-'))
                    f2.append(self.get_cnf_id(self.var_p[i, j]))
                    self.clause.append(f2)

                    f3 = []
                    f3.append(self.get_cnf_id(self.var_v[i, j+1]))
                    f3.append(self.get_cnf_id(self.var_l[j], '-'))
                    f3.append(self.get_cnf_id(self.var_p[i, j], '-'))
                    self.clause.append(f3)

        def cons_7(self): # Exactly one S[j1] \/ l[j] S[j2]... \/ l[j] S[jf] \/ l[j]
            for j in range(1, self.N + 1):
                for f in range(1, self.K+1):
                    or_f = []
                    or_f.append(self.get_cnf_id(self.var_S[j, f]))
                    or_f.append(self.get_cnf_id(self.var_l[j]))

                for a in range(2, len(or_f) + 1):
                    for b in itertools.combinations(or_f, r=a):
                        new_f = or_f.copy()
                        for c in b:
                            ins = new_f.index(c)
                            new_f[ins] = -c
                        self.clause.append(new_f)

        def cons_8(self):
            for j in range(1, self.N-1):
                for f in range(2, self.K+1):
                    f = []
                    f.append(self.get_cnf_id(self.var_S[j+1, f]))
                 #   f.append(self.get_cnf_id(self.var_l[j]))
                  #  for ff in range(1, f):
                   #     f.append(self.get_cnf_id(self.var_S[j, ff]))
                    self.clause.append(f)







        cons_1(self)
        cons_2(self)
        cons_3(self)
        cons_4(self)
        cons_5(self)
        cons_6(self)
        cons_7(self)
        cons_8(self)

    '''
    pysmt
    def encode_constraints(self):  # Encode the constraints in paper

        def cons_1(self): #All data are valid at the first node
            formulas = []
            for i in range(1, self.I+1):
                formulas.append(self.var_v[i,1])
            return formulas

        def cons_2(self):
            formulas = []
            for i in range(1, self.I+1):
                for j in range(1, self.N):
                    for f in range(1, self.K + 1):
                        or_formulas = []
                        if self.data_features[i][f-1]:
                            or_formulas.append(And(self.S[j, f], self.var_t[j]))
                        else:
                            or_formulas.append(And(self.S[j, f], Not(self.var_t[j])))
                        formulas.append(Iff(self.ex[i, j], Or(or_formulas)))
            return formulas

        #def cons_3(self): # Ensure an item does not have two consecutive invalid nodes.

        all_cons = [cons_1, cons_2]
        all_f = []
        for c in all_cons:
            all_f.append(And(c(self)))
        formulas = And(all_f)
        return formulas

    def establish_solver(self):
        self.formulas = self.encode_constraints()
        target_logic = get_logic(self.formulas)
        print("Target Logic: %s" % target_logic)
        self.solver = Solver(logic=target_logic)
        self.solver.add_assertion(self.formulas)
        self.num_sol = 0

    def solve_using_solver(self):
        while self.solver.solve():
            all_vars_sol_noc = [EqualsOrIff(var, self.solver.get_value(var)) for var in self.all_vars if str(var)[1] != 'c']
            basic_vars_sol = [(str(var), self.solver.get_value(var).is_true()) for var in self.all_basic_vars]
            self.solver.add_assertion(Not( And( all_vars_sol_noc ) ) )
            return tuple(basic_vars_sol)
        return None
    '''

    # pycosat



