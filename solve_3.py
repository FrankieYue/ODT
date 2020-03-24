import numpy as np
from util.DSSolver import DSSolver
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
filename = "weather.csv"
#filename = "mouse-un.csv"
'''
feature_names, feature_vars, data_features, data_classes = data_processing(filename)
print(feature_names)
print(feature_vars)
print(data_features)
print(data_classes)

'''
if __name__ == "__main__":
    feature_names, feature_vars, data_features, data_classes = data_processing(filename)
    K = data_features.shape[1]
    found = False
    data = (data_features, data_classes)
    num_literal = 1 #The number of decision nodes
    N = num_literal * 2 + 1
    DDS_solver = DSSolver(K, N, data)

    DDS_solver.encode_constraints()
    print(DDS_solver.clause)
    print(DDS_solver.var2ids)
    print(DDS_solver.ids2var)
    print(DDS_solver.sig)
    print(DDS_solver.var_S)