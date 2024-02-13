
from sage.all import *
import argparse
import copy
import itertools

class Equation:
    def __init__(self, args):
        self.dst = args[0]

        if(len(args) == 3):
            if(args[2][0] == "~"):
                v = '1'
                args[2] = args[2][1:]
                self.op = '+'
                self.arg1 = args[2]
                self.arg2 = v
            else:
                self.op = ''
                self.arg1 = args[2]
                self.arg2 = ''
        else:
            assert(len(args) == 5)
            self.op = args[3]
            self.arg1 = args[2]
            self.arg2 = args[4]

    def evaluate(self, R: BooleanPolynomialRing, evaluate_over_R):
        e1 = self.arg1
        e2 = self.arg2

        if(self.op == '+'):
            eval = R(evaluate_over_R[e1] + evaluate_over_R[e2])
        elif(self.op == '*'):
            eval = R(evaluate_over_R[e1] * evaluate_over_R[e2])
        else:
            eval = evaluate_over_R[e1]

        return eval


class Circuit:

    def __init__(self, circuit_file=None):
        if(circuit_file != None):
            self.read_input_circuit(circuit_file)

    def read_input_circuit(self,circuit_file):
        f1 = open(circuit_file)
        lines = f1.readlines()
        f1.close()
        
        if("ORDER" in lines[0]):
            lines = lines[1:]
        
        nb_shares = int(lines[0].split()[1])
        nb_duplications = int(lines[1].split()[1])
        
        input_names = lines[2].split()[1:]
        randoms = lines[3].split()[1:]
        output_names = lines[4].split()[1:]

        assert(len(output_names) == 1)
        
        lines = lines[5:]
        
        inputs = []
        input_name_from_duplicate = dict()
        
        for x in range(len(input_names)):
            for i in range(nb_shares):
                inputs.append(input_names[x]+str(i))
                for j in range(nb_duplications):
                    input_name_from_duplicate[input_names[x]+str(i)+"_"+str(j)] = input_names[x]+str(i)
        self.boolean_vars = inputs+randoms

        eqs = []

        for line in lines:
            if (line == '\n') or (len(line)==0) or (line[0] == "#"):
                continue
            args = line.split()
            if(len(args) == 0):
                continue
            if("![" in args):
                args.remove("![")
                args.remove("]")
            if(args[-1][0] == "#"):
                args = args[:len(args)-1]

            eqs.append(Equation(args))
            
        outputs = []
        self.output_idx_from_duplicate = dict()
        for o in output_names:
            for i in range(nb_shares):
                for j in range(nb_duplications):
                    outputs.append(o+str(i)+"_"+str(j))
                    self.output_idx_from_duplicate[o+str(i)+"_"+str(j)] = i

        eqs_outputs = []
        idx = []
        for i in range(len(eqs)-1, -1, -1):
            if(eqs[i].dst in outputs):
                idx.append(i)
                outputs.remove(eqs[i].dst)

        for i in idx:
            eqs_outputs.append(eqs.pop(i))

        self.inputs = inputs
        self.randoms = randoms
        self.input_name_from_duplicate = input_name_from_duplicate
        self.eqs = eqs
        self.eqs_outputs = eqs_outputs
        self.nb_shares = nb_shares
        self.nb_duplications = nb_duplications
        self.evaluate_over_R, self.evaluate_outputs_over_R = self.evaluate_circuit()
    
    def evaluate_circuit(self, faults=[], set=True):
        R = BooleanPolynomialRing(names=self.boolean_vars)
        evaluate_over_R = dict()
        for v in self.randoms+['0','1']:
            if(v in faults):
                if(set):
                    evaluate_over_R[v] = R(1)
                else:
                    evaluate_over_R[v] = R(0)
            else:
                evaluate_over_R[v] = R(v)

        for v in self.input_name_from_duplicate:
            if(v in faults):
                if(set):
                    evaluate_over_R[v] = R(1)
                else:
                    evaluate_over_R[v] = R(0)
            else:
                evaluate_over_R[v] = R(self.input_name_from_duplicate[v])

        for k in self.eqs:
            if(k.dst in faults):
                if(set):
                    evaluate_over_R[k.dst] = R(1)
                else:
                    evaluate_over_R[k.dst] = R(0)
            else:
                evaluate_over_R[k.dst] = k.evaluate(R, evaluate_over_R)

        evaluate_outputs_over_R = dict()
        for k in self.eqs_outputs:
            if(k.dst in faults):
                if(set):
                    evaluate_outputs_over_R[k.dst] = R(1)
                else:
                    evaluate_outputs_over_R[k.dst] = R(0)
            else:
                evaluate_outputs_over_R[k.dst] = k.evaluate(R, evaluate_over_R)

        return evaluate_over_R, evaluate_outputs_over_R
    
    def print_evaluation(self, faults=[], set=True):
        evaluate_over_R, evaluate_outputs_over_R = self.evaluate_circuit(faults, set)
        for e in evaluate_over_R.keys():
            print(e, " = ", evaluate_over_R[e])
        for e in evaluate_outputs_over_R.keys():
            print(e, " = ", evaluate_outputs_over_R[e])
        print("")


    def can_faulty_circuit_be_corrected(self, faults, set, original_evaluate_outputs_over_R):
        evaluate_over_R, evaluate_outputs_over_R = self.evaluate_circuit(faults, set)

        bound = (self.nb_duplications - 1) // 2

        ks = [0] * self.nb_shares
        for o in evaluate_outputs_over_R.keys():
            #print(o, " = ",original_evaluate_outputs_over_R[o], ", ", evaluate_outputs_over_R[o])
            if(original_evaluate_outputs_over_R[o] != evaluate_outputs_over_R[o]):
                ks[self.output_idx_from_duplicate[o]] += 1

        for k in ks:
            if(k > bound):
                return False
            
        return True
    
    def get_input_comb_rec(self, input_idx):
        if(input_idx >= len(self.inputs)):
            return []
        
        combs = self.get_input_comb_rec(input_idx +1)
        capacity = (self.nb_duplications-1)//2

        names = []
        for j in range(self.nb_duplications):
            names.append(self.inputs[input_idx] + "_" + str(j))
        
        new_combs = []
        for comb in itertools.combinations(names, capacity):
            if(len(combs) == 0):
                new_combs.append(list(comb))
            else:
                for c in combs:
                    new_combs.append(list(c) + list(comb))

        return new_combs

    
    def get_input_combs(self):
        return self.get_input_comb_rec(0)

    def get_uncorrected_faulty_combs(self, k, property, set):
        names = []
        for e in self.eqs:
            names.append(e.dst)
        for e in self.randoms:
            names.append(e)
        for e in self.eqs_outputs:
            names.append(e.dst)

        length = len(self.eqs) + len(self.randoms) + len(self.eqs_outputs)

        if(property == "CRPC"):
            input_combs = self.get_input_combs()
            print("len input combs = ", len(input_combs))

        scenarios = []
        if(property == "CRPC"):
            for prefix in input_combs:
                print(prefix)
                sc = []
                for i in range(1,k+1):
                    for comb in itertools.combinations(names, i):
                        comb_rands = []
                        for c in comb:
                            if(c in self.randoms):
                                comb_rands.append(c)

                        if(len(comb_rands) > 0):
                            evaluate_over_R, evaluate_outputs_over_R = self.evaluate_circuit(comb_rands, set)
                        else:
                            evaluate_outputs_over_R = self.evaluate_outputs_over_R

                        if(not(self.can_faulty_circuit_be_corrected(prefix + list(comb), set, evaluate_outputs_over_R))):
                            sc.append(comb)
                print(len(sc))
                scenarios.append(sc)
        else:
            for i in range(1,k+1):
                print("Testing combinations of ", i," faults...")
                for comb in itertools.combinations(names, i):
                    comb_rands = []
                    for c in comb:
                        if(c in self.randoms):
                            comb_rands.append(c)

                    if(len(comb_rands) > 0):
                        evaluate_over_R, evaluate_outputs_over_R = self.evaluate_circuit(comb_rands, set)
                    else:
                        evaluate_outputs_over_R = self.evaluate_outputs_over_R

                    if(not(self.can_faulty_circuit_be_corrected(comb, set, evaluate_outputs_over_R))):
                        scenarios.append(comb)

        return length, scenarios



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-f", help="File", type = str)

    parser.add_argument("-k", help="Number of faults to consider", type=int)
    parser.add_argument("-s", help="Type of faults (0:reset, 1:set)", type=int, default = 1)
    parser.add_argument("-p", help="Property", type=str, choices=["CRP","CRPC"], default="CRP")
    args = parser.parse_args()

    c = Circuit(args.f)
    c.print_evaluation(faults=[0])

    assert(args.p is not None)


    set = True
    if(args.s == 0):
        set = False

    length, scenarios = c.get_uncorrected_faulty_combs(args.k, args.p, set)

    f = 0.01
    if(property == "CRPC"):
        print(length)
        res = 0
        for sc in scenarios:
            inter_res = 0
            for s in sc:
                inter_res = inter_res + ((f**(len(s))) * (1-f)**(length-len(s)))
            if(inter_res > res):
                res = inter_res
        print("mu = ",res) 
    else:
        res = 0
        for s in scenarios:
            res = res + ((f**(len(s))) * (1-f)**(length-len(s)))
        print("mu = ",res) 

        file = open(args.f+"_faulty_scenarios_k"+str(args.k)+"_f"+str(args.s)+"_"+str(args.p), "w")
        file.write(str(len(scenarios)) +  "\n")
        for s in scenarios:
            line = str(len(s))+", "
            for e in s[:-1]:
                line = line + e + ", "
            line = line + s[-1]
            file.write(line+"\n")
        file.close()


if __name__ == "__main__":
    main()