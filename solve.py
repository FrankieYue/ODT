import numpy as np
from util.BuildDT import Build_SAT_DT
from util.DecisionTree import DT

def data_processing(file_name):
    data_path = "data/" + file_name
    data = open(data_path)
    feature_names = data.readline().strip("\n").split(",")
    feature_vars = [[] for i in range(len(feature_names))]
    num_examples = 0

    end = False
    while not end:
        line = data.readline().strip("\n").split(",")
        if line == ['']:
            end = True
            data.close()
        else:
            for i, f in enumerate(line):
                if f not in feature_vars[i]:
                    feature_vars[i].append(f)
            num_examples += 1
    num_features = 0
    for i in range(len(feature_names) - 1):
        c = len(feature_vars[i]) if len(feature_vars[i]) > 2 else 1
        num_features += c

    data_features = np.zeros(shape=(num_examples, num_features), dtype=np.int)
    data_classes = np.zeros(shape=(num_examples), dtype=np.int)

    data = open(data_path)
    data.readline()  # Skip the header
    end = False
    curr_exmaple_index = 0
    first_eg = True

    while not end:
        line = data.readline().strip("\n").split(",")
        if line == ['']:
            end = True
            data.close()
        else:
            for i, f in enumerate(line[:-1]):
                num_prev_vars = 0
                for j in range(i):
                    num_prev_vars += len(feature_vars[j]) if len(feature_vars[j]) > 2 else 1

                if len(feature_vars[i]) > 2:
                    curr_f_index = feature_vars[i].index(f) + num_prev_vars
                    data_features[curr_exmaple_index, curr_f_index] = 1
                else:
                    curr_f_index = num_prev_vars
                    if first_eg:
                        first_line = line
                        data_features[0, curr_f_index] = 0 if str(first_line[i]).strip().upper() == 'FALSE' or str(first_line[i]).strip() == '0' \
                                                              or str(first_line[i]).strip().upper() == 'NO' or str(first_line[i]).strip().upper() == 'WEAK' \
                                                              or str(first_line[i]).strip().upper() == 'NORMAL'else 1
                        first_eg = False
                    else:
                        data_features[curr_exmaple_index, curr_f_index] = data_features[0, curr_f_index] if line[i] == first_line[i] else (data_features[0, curr_f_index] + 1) % 2

            data_classes[curr_exmaple_index] = 0 if str(line[-1]).strip().upper() == 'FALSE' or str(line[-1]).strip() == '0'\
                                                    or str(line[-1]).strip().upper() == 'NO' or str(first_line[i]).strip().upper() == 'WEAK' \
                                                    or str(first_line[i]).strip().upper() == 'NORMAL' else 1
            curr_exmaple_index += 1


    return feature_names, feature_vars, data_features, data_classes


# max_nodes = 9 # It means minimun literals is 9
#filename = "weather.csv"
filename = "mouse-un.csv"

#feature_names, feature_vars, data_features, data_classes = data_processing(filename)
#print(feature_names)
#print(feature_vars)
#print(data_features)
#print(data_classes)



if __name__ == "__main__":
    feature_names, feature_vars, data_features, data_classes = data_processing(filename)
    K = data_features.shape[1]
    found = False
    data = (data_features, data_classes)
    num_literal = 1 #The number of decision nodes

    while not found:
        N = num_literal * 2 + 1
        sat_dt_solver = Build_SAT_DT(K, N, data)
        dt = DT(K, N)
        sat_dt_solver.establish_solver()
        all_sol = set()
        num_sol = 0
        end = False

        while not end:
            sol = sat_dt_solver.solve_using_solver()
            if sol is not None:
                found = True
                print("\nSolution", num_sol+1)
                print(sol)
                num_sol += 1
                all_sol.add(sol)
                dt.parse_solution(sol)
                dt.validate(data_features, data_classes)
                dt.print_DT()
                print("The number of decision nodes is {0}".format(num_literal))
                dt.draw(len(all_sol), filename[:-4])

                if N >= 100:
                    end = True
            else:
                if not found:
                    num_literal += 1
                end = True
        if N > 99:
            break

    if found:
        print("\nSolutions found, the minimun number of nodes is {0}".format(N))
        print("The minimun number of decision sets is {0}".format(num_literal))
    else:
        print("Solution not found when the maximum number of decision sets is 99")
