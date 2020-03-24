import numpy as np
from pysmt.shortcuts import *
from pysmt.oracles import get_logic
from math import ceil, floor

class Build_SAT_DT():
    def __init__(self, K, N, data):
        self.N = N
        self.K = K
        self.LR = lambda i: set(filter(lambda jj: jj % 2 == 0, [j for j in range(i+1, min(2 * i, N - 1) + 1)]))
        self.RR = lambda i: set(filter(lambda jj: jj % 2 == 1, [j for j in range(i+2, min(2 * i + 1, N) + 1)]))
        self.v = np.empty(shape=(N+1), dtype=object)
        self.l = np.empty(shape=(N+1, N+1), dtype=object)
        self.r = np.empty(shape=(N+1, N+1), dtype=object)
        self.p = np.empty(shape=(N+1, N), dtype=object)
        self.a = np.empty(shape=(K+1, N+1), dtype=object)
        self.u = np.empty(shape=(K+1, N+1), dtype=object)
        self.d0 = np.empty(shape=(K+1, N+1), dtype=object)
        self.d1 = np.empty(shape=(K+1, N+1), dtype=object)
        self.c = np.empty(shape=(N + 1), dtype=object)
        self.lam = np.empty(shape=(N//2 + 1, N+1), dtype=object)
        self.tau = np.empty(shape=(N + 1, N+1), dtype=object)

        self.pos_example_features = set()  # Features with positive examples
        self.neg_example_features = set()  # Features with negative examples
        for data_feature, data_class in zip(*data):
            if data_class == 1:
                self.pos_example_features.add(tuple(data_feature))
            else:
                self.neg_example_features.add(tuple(data_feature))

        # Non basic keys: "p", "u"... Basic keys are the DT keys for producing a solution to update a DT
        self.basic_keys = ("v", "l", "r", "a", "c") # DT variables
        self.all_basic_vars = set() # All DT variables With indices
        self.all_vars = set() # All vars including basic and non-basic vars With indices

        self.solver = None
        self.formulas = None
        self.num_sol = None
        #self.p_sol = None

        # Add variable and its type. Example format: var_with_index: 'v[1]', var_name: 'v'
     #   '''
        def add_key(var_with_index, var_name):
            if var_name in self.basic_keys:
                self.all_basic_vars.add(var_with_index)
            self.all_vars.add(var_with_index)

        def add_vars_1d(vars, var_name):
            for i in range(1, vars.shape[0]):
                vars[i] = Symbol(var_name + "[" + str(i) + "]")
                add_key(vars[i], var_name)

        def add_vars_2d(vars, var_name):
            if var_name == "p":
                for i in range(1, vars.shape[1]):  # arr.shape[0] shows the number of rows
                    for j in self.LR(i) | self.RR(i):  # for all i descendants
                        vars[j, i] = Symbol(var_name + "[" + str(j) + ',' + str(i) + "]")
                        add_key(vars[j, i], var_name)
            else:
                for i in range(1, vars.shape[0]):
                    if var_name != 'l' and var_name != 'r':
                        for j in range(1, vars.shape[1]):
                            vars[i, j] = Symbol(var_name + "[" + str(i) + "," + str(j) + "]")
                            add_key(vars[i, j], var_name)

                    elif var_name == 'l':
                        for j in self.LR(i):
                            vars[i, j] = Symbol(var_name + "[" + str(i) + "," + str(j) + "]")
                            add_key(vars[i, j], var_name)

                    elif var_name == 'r':
                        for j in self.RR(i):
                            vars[i, j] = Symbol(var_name + "[" + str(i) + "," + str(j) + "]")
                            add_key(vars[i, j], var_name)

        def add_vars_addition(vars, var_name):
            if var_name == "lam":
                for i in range(1, vars.shape[1]):
                    for t in range(i//2 + 1):
                        vars[t, i] = Symbol(var_name + "[" + str(t) + "," + str(i) + "]")

            elif var_name == "tau":
                for i in range(1, vars.shape[1]):
                    for t in range(i+1):
                        vars[t, i] = Symbol(var_name + "[" + str(t) + "," + str(i) + "]")

        add_vars_1d(self.v, "v")
        add_vars_2d(self.l, "l")
        add_vars_2d(self.r, "r")
        add_vars_2d(self.p, "p")
        add_vars_2d(self.a, "a")
        add_vars_2d(self.u, "u")
        add_vars_2d(self.d0, "d0")
        add_vars_2d(self.d1, "d1")
        add_vars_1d(self.c, "c")
        add_vars_addition(self.lam, "lam")
        add_vars_addition(self.tau, "tau")

    def print_aa(self):
        print(self.l)

    def encode_constraints(self):  # Encode the constraints in paper

        def cons_1(self):
            formulas = []
            formulas.append(Not(self.v[1]))
            return formulas

        def cons_2(self):
            formulas = []
            for i in range(1, self.N+1):
                for j in self.LR(i):
                    formulas.append(self.v[i].Implies(Not(self.l[i, j])))
            return formulas

        def cons_3(self):
            formulas = []
            for i in range(1, self.N+1):
                for j in self.LR(i):
                    formulas.append(Iff(self.l[i, j], self.r[i, j+1]))
            return formulas


        def cons_4(self):
            formulas = []
            for i in range(1, self.N + 1):
                sum_f = []
                for j in self.LR(i):
                    sum_f.append(self.l[i, j])
                f = Not(self.v[i]).Implies(ExactlyOne(sum_f))
                formulas.append(f)
            return formulas

        def cons_5(self):
            formulas = []
            for i in range(1, self.N):
                for j in self.LR(i):
                    formulas.append(Iff(self.p[j, i], self.l[i, j]))
                for j in self.RR(i):
                    formulas.append(Iff(self.p[j, i], self.r[i, j]))
            return formulas

        def cons_6(self):
            formulas = []
            for j in range(2, self.N + 1):
                sum_f = []
                for i in range(j//2, min(j - 1, self.N) + 1):
                    if j in self.LR(i) | self.RR(i):
                        sum_f.append(self.p[j, i])
                f = ExactlyOne(sum_f)
                formulas.append(f)
            return formulas

        def cons_7(self):
            formulas = []
            for r in range(1, self.K+1):
                formulas.append(Not(self.d0[r, 1]))
                for j in range(2, self.N+1):
                    f1 = self.d0[r, j]
                    f2_or = []
                    for i in range(j//2, j):
                        if j in self.LR(i) | self.RR(i):
                            f2_or.append(And(self.p[j, i], self.d0[r, i]))
                            if j in self.RR(i):
                                f2_or.append(And(self.a[r, i], self.r[i, j]))
                    formulas.append(Iff(f1, Or(f2_or)))
            return formulas


        def cons_8(self):
            formulas = []
            for r in range(1, self.K + 1):
                for j in range(2, self.N + 1):
                    f2_or = []
                    for i in range(j//2, j):
                        if j in self.LR(i) | self.RR(i):
                            f2_or.append(And(self.p[j, i], self.d1[r, i]))
                            if j in self.LR(i):
                                f2_or.append(And(self.a[r, i], self.l[i, j]))
                    f = Iff(self.d1[r, j], Or(f2_or))
                    all_f.append(f)
                f = Not(self.d1[r, 1])
                formulas.append(f)
            return formulas


        def cons_9(self):
            formulas = []
            for r in range(1, self.K + 1):
                for j in range(1, self.N + 1):
                    fa_and = []
                    fb_or = []
                    for i in range(j//2, j):
                        if i != 0 and j in self.LR(i) | self.RR(i):
                            fa_and.append(And(self.u[r, i], self.p[j, i]).Implies(Not(self.a[r, j]))) #9a
                            fb_or.append(And(self.u[r, i], self.p[j, i])) #9b
                    fa = And(fa_and)
                    formulas.append(fa)
                    fb = Iff(self.u[r, j], Or(self.a[r, j], Or(fb_or)))
                    formulas.append(fb)
            return formulas

        def cons_10(self):
            formulas = []
            for j in range(1, self.N+1):
                f1 = Not(self.v[j])
                sum_f = []
                for r in range(1, self.K+1):
                    sum_f.append(self.a[r, j])
                f2 = ExactlyOne(sum_f)
                formulas.append(f1.Implies(f2))
            return formulas

        def cons_11(self):
            formulas = []
            for j in range(1, self.N + 1):
                f1 = self.v[j]
                f2_and = []
                for r in range(1, self.K+1):
                    f2_and.append(Not(self.a[r, j]))
                f2 = And(f2_and)
                formulas.append(f1.Implies(f2))
            return formulas

        def cons_12(self):
            formulas = []
            for pos_features in self.pos_example_features:
                for j in range(1, self.N+1):
                    f1 = And(self.v[j], Not(self.c[j]))
                    f2_or = []
                    for r in range(1, self.K+1):
                        example_feature_index = r - 1
                        if pos_features[example_feature_index]:
                            f2_or.append(self.d1[r, j])
                        else:
                            assert not pos_features[example_feature_index]
                            f2_or.append(self.d0[r, j])
                    f2 = Or(f2_or)
                    formulas.append(f1.Implies(f2))

            return formulas

        def cons_13(self):
            formulas = []
            for pos_features in self.neg_example_features:
                for j in range(1, self.N + 1):
                    f1 = And(self.v[j], self.c[j])
                    f2_or = []
                    for r in range(1, self.K + 1):
                        example_feature_index = r - 1
                        if pos_features[example_feature_index]:
                            f2_or.append(self.d1[r, j])
                        else:
                            assert not pos_features[example_feature_index]
                            f2_or.append(self.d0[r, j])
                    f2 = Or(f2_or)
                    formulas.append(f1.Implies(f2))
            return formulas

        def add_cons_1(self): # Additional inference constraints
            formulas = []
            for i in range(1, self.N + 1):
                formulas.append(self.lam[0, i]) # Add_cons_1a
                formulas.append(self.tau[0, i]) # Add_cons_2a
                for t in range(1, floor(i / 2) + 1): # Add_cons_1b
                    f1 = self.lam[t, i]
                    if ((i - 1) // 2) < t:
                        f2 = Or(self.v[i])
                    else:
                        f2 = Or(self.lam[t, i - 1], And(self.lam[t - 1, i - 1], self.v[i]))
                    formulas.append(Iff(f1, f2))
                for t in range(1, i + 1): # Add_cons_2b
                    f3 = self.tau[t, i]
                    if i - 1 < t:
                        f4 = Or(Not(self.v[i]))
                    else:
                        f4 = Or(self.tau[t, i - 1], And(self.tau[t - 1, i - 1], Not(self.v[i])))
                    formulas.append(Iff(f3, f4))
            return formulas

        def add_cons_2(self): # Proposition 2 constraint
            formulas = []
            for i in range(1, self.N+1):
                for t in range(1, i//2 + 1):
                    if self.lam[t, i] == 1:
                        formulas.append(And(Not(self.l[i, 2 * (i-t+1)]), Not(self.r[i, 2 * (i-t+1) + 1])))

            return formulas

        def add_cons_3(self): # Proposition 3 constraint
            formulas = []
            for i in range(1, self.N+1):
                for t in range(i//2 + 1, i + 1):
                    if 2*(t-1) in self.LR(i) and 2*t-1 in self.RR(i):
                        formulas.append( self.tau[t, i].Implies(And( Not( self.l[i,2*(t-1)] ), Not( self.r[i,2*t-1]) ) ) )
            return formulas

        all_cons = [cons_1, cons_2, cons_3, cons_4, cons_5, cons_6, cons_7, cons_8, cons_9, cons_10,
                   cons_11, cons_12, cons_13, add_cons_1, add_cons_2, add_cons_3]

        all_f = []
        for cons in all_cons:
            all_f.append(And(cons(self)))

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
            #all_vars_sol = [EqualsOrIff(var, self.solver.get_value(var)) for var in self.all_vars]
            all_vars_sol_noc = [EqualsOrIff(var, self.solver.get_value(var)) for var in self.all_vars if str(var)[1] != 'c']
            #curr_vars_sol = [(str(var), self.solver.get_value(var).is_true()) for var in self.all_basic_vars if str(var)[1] != 'c']
            basic_vars_sol = [(str(var), self.solver.get_value(var).is_true()) for var in self.all_basic_vars]
         #   self.solver.add_assertion(Not( And( all_vars_sol ) ) )
            self.solver.add_assertion(Not( And( all_vars_sol_noc ) ) )
          #  if self.p_sol != curr_vars_sol:
           #     self.num_sol += 1
            #    print(self.p_sol)
             #   print(curr_vars_sol)
            #self.p_sol = curr_vars_sol
            return tuple(basic_vars_sol)
        return None
        







