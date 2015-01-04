import math
import random
import sys
try:
    from src.gimpy import Tree
except ImportError:
    from coinor.gimpy import Tree
try:
    from src.blimpy import PriorityQueue
except ImportError:
    from coinor.blimpy import PriorityQueue
import time
from cylp.cy import CyClpSimplex
from cylp.py.modeling import CyLPArray, CyLPModel
import importlib as ilib
import numpy as np
from scipy import sparse

# parent of root node.
DUMMY_NODE = 'dummy_node'
# branching strategies
MOST_FRACTIONAL = 'Most Fractional'
INTERDICTION_BRANCHING = 'Interdiction Branching'
# search strategies
DEPTH_FIRST = 'Depth First'
BEST_FIRST = 'Best First'
BEST_ESTIMATE = 'Best Estimate'
INFINITY = sys.maxint

etol = 1e-7

class InterdictionTree(Tree):
    
    def __init__(self, **attrs):
        Tree.__init__(self, **attrs)
        self._incumbent_value = None
        self.branch_strategy = INTERDICTION_BRANCHING
        self.search_strategy = BEST_FIRST
        self.branch_on_fractional = False
        if self.get_layout() == 'dot2tex':
            print "Dot2Tex not supported..."
            self.display_mode = 'off'
        else:
            cluster_attrs = {'name':'Key', 'label':'Key', 'fontsize':'12'}
            self.add_node('C', label = 'Candidate', style = 'filled',
                          color = 'yellow', fillcolor = 'yellow')
            self.add_node('I', label = 'Infeasible', style = 'filled',
                          color = 'orange', fillcolor = 'orange')
            self.add_node('S', label = 'Solution', style = 'filled',
                          color = 'lightblue', fillcolor = 'lightblue')
            self.add_node('P', label = 'Pruned', style = 'filled',
                          color = 'red', fillcolor = 'red')
            self.add_node('PC', label = 'Pruned \n Candidate', style = 'filled',
                          color = 'red', fillcolor = 'yellow')
        self.add_edge('C', 'I', style = 'invisible', arrowhead = 'none')
        self.add_edge('I', 'S', style = 'invisible', arrowhead = 'none')
        self.add_edge('S', 'P', style = 'invisible', arrowhead = 'none')
        self.add_edge('P', 'PC', style = 'invisible', arrowhead = 'none')
        self.create_cluster(['C', 'I', 'S', 'P', 'PC'], cluster_attrs)

    def GenerateRandomMILP(self, VARIABLES, CONSTRAINTS, density = 0.2,
                           maxObjCoeff = 10, maxConsCoeff = 10, 
                           tightness = 2, rand_seed = 2):
        random.seed(rand_seed)
        self.VARIABLES = VARIABLES
        self.CONSTRAINTS = CONSTRAINTS
        self.OBJ = dict((i, random.randint(1, maxObjCoeff)) for i in VARIABLES)
        self.MAT = dict(((i, j), random.randint(1, maxConsCoeff) 
                        if random.random() <= density else 0)
                for i in CONSTRAINTS for j in VARIABLES)
        self.RHS = dict((i, random.randint(int(len(VARIABLES)*density*maxConsCoeff/tightness),
                                  int(len(VARIABLES)*density*maxConsCoeff/1.5)))
                                  for i in CONSTRAINTS)
    
    def BranchAndBound(self, complete_enumeration = False,
                       display_interval = None, debug_print = False,
                       max_iter_num = 100000):

        #====================================
        # Initialize
        #====================================
        
        # The number of LP's solved, and the number of nodes solved
        self.node_count = 1
        self.real_node_count = 1
        iter_count = 0
        lp_count = 0
        numVars = len(self.OBJ)
        numCons = len(self.RHS)
        sense = self.SENSE[1]
        INFINITY = CyClpSimplex().getCoinInfinity()
        opt = None
        # List of incumbent solution variable values
        print "==========================================="
        print "Starting Branch and Bound"
        if self.branch_strategy is MOST_FRACTIONAL:
            print "Most fractional variable"
        elif self.branch_strategy is INTERDICTION_BRANCHING:
            print "Interdiction branching"
        else:
            print "Unknown branching strategy %s" %self.branch_strategy
        if self.search_strategy is DEPTH_FIRST:
            print "Depth first search strategy"
        elif self.search_strategy is BEST_FIRST:
            print "Best first search strategy"
        else:
            print "Unknown search strategy %s" %self.search_strategy
        print "==========================================="
        # List of candidate nodes
        self.Q = PriorityQueue()
        # The current tree depth
        cur_depth = 0
        cur_index = 0
        # Timer
        timer = time.time()
        self.Q.push(0, -INFINITY, (0, None, None, None))

        #====================================
        # Main Loop
        #====================================

        while not self.Q.isEmpty():
            
            if iter_count >= max_iter_num:
                print "Maximum iterations reached..."
                break

            #====================================
            # Set Up
            #====================================

            infeasible = False
            integer_solution = False
            cur_index, parent, relax, branch_vars = self.Q.pop()
            if cur_index is not 0:
                cur_depth = self.get_node_attr(parent, 'level') + 1
            else:
                cur_depth = 0
            print ""
            print "----------------------------------------------------"
            print ""
            print "Node: %s, Depth: %s, " %(cur_index, cur_depth),
            if self.SENSE[0] == 'Max':
                print "LB: %s" %(self._incumbent_value)
            else:
                print "UB: %s" %(self._incumbent_value)
            if (relax is not None and self._incumbent_value is not None and
                ((self.SENSE[0] == 'Max' and relax <= self._incumbent_value + 1 - etol) or
                 (self.SENSE[0] == 'Min' and relax >= self._incumbent_value - 1 + etol))):
                print "Node pruned immediately by bound"
                self.set_node_attr(parent, 'color', 'red')
                self.real_node_count -= 1
                continue

            #====================================
            # Solve LP Relaxation
            #====================================

            # Fix all prescribed variables
            branch_var_set = {}
            if cur_index is not 0:
                branch_var_set.update(branch_vars)
                var_set_to_one = -1
                for i in branch_var_set:
                    if branch_var_set[i] == 1:
                        var_set_to_one = i
                if var_set_to_one is -1:
                    var_set_to_zero = branch_var_set.keys()[0]
                pred = parent
                while str(pred) is not '0':
                    pred_branch_var_set = self.get_node_attr(pred, 'branch_var_set')
                    branch_var_set.update(pred_branch_var_set)
                    pred = self.get_node_attr(pred, 'parent')
            print "Branching set:"
            print branch_var_set
            # Compute lower bound by LP relaxation
            self.ADJ_RHS = CyLPArray(self.RHS)
            eliminate_fixed = True
            if (eliminate_fixed):
                for j in branch_var_set:
                    if branch_var_set[j] == 1:
                        for i in self.MAT.getcol(j).indices:
                            print self.RHS[i], self.ADJ_RHS[i], self.MAT[i,j] 
                            self.ADJ_RHS[i] -= self.MAT[i,j]
                            print self.RHS[i], self.ADJ_RHS[i] 
                            
                OBJ_OFFSET = sum([self.OBJ[j] for j in branch_var_set if branch_var_set[j] == 1])
                k = 0
                FREE_VARIABLES = {}
                for i in range(numVars):
                    if i not in branch_var_set:
                        FREE_VARIABLES[i] = k
                        k += 1
                if debug_print: 
                    print 'Objective offset: ', OBJ_OFFSET 
            else:
                OBJ_OFFSET = 0
                FREE_VARIABLES = {(i, i) for i in range(numVars)}
            if FREE_VARIABLES != {}:
                lp = CyClpSimplex()
                A = self.MAT[:,FREE_VARIABLES.keys()]
                b = CyLPArray(self.ADJ_RHS)
                x = lp.addVariable('x', len(FREE_VARIABLES))
                lp += 0 <= x <= 1
                if not eliminate_fixed:
                    for j in branch_var_set:
                        lp += x[j] == branch_var_set[j]
                for i in range(numCons):
                    if sense[i] == '<=':
                        lp += -A.getrow(i) * x >= -self.ADJ_RHS[i]
                    elif sense[i] == '>=':
                        lp += A.getrow(i) * x >= self.ADJ_RHS[i]
                    else:
                        lp += A.getrow(i) * x == self.ADJ_RHS[i]                         
                c = CyLPArray([self.OBJ[j] for j in FREE_VARIABLES])
                lp.objective = -c * x if self.SENSE[0] == 'Max' else c * x
                lp.primal(startFinishOptions = 'x')
                lp_count = lp_count + 1
                status = lp.getStatusCode()
                # Check infeasibility
                infeasible = (status == 1)
                
                if debug_print:
                    print "Duals on constraints in LP relaxation:", lp.dualConstraintSolution
                    print "Reduced costs on variables in LP relaxation:", lp.reducedCosts
                if not infeasible:
                    relax = lp.objectiveValue + OBJ_OFFSET
            else:
                print "All variables fixed...no LP to solve" 
                infeasible = False
                for i in self.ADJ_RHS:
                    if i < 0:
                        infeasible = True
                        break
                if not infeasible:
                    relax = OBJ_OFFSET
            
            #====================================
            # Process Result
            #====================================
            
            # Print status
            if infeasible:
                print "Node status: infeasible"
                relax = 0
            else:
                print "Node status: feasible with obj = %s" %relax
                self.sol = lp.primalVariableSolution['x']
                if isInt(self.sol):
                    integer_solution = True
                else:
                    integer_solution = False
                if (integer_solution and 
                    (self._incumbent_value is None or 
                    (self.SENSE[0] == 'Max' and relax > self._incumbent_value) or
                    (self.SENSE[0] == 'Min' and relax < self._incumbent_value))):
                    self._incumbent_value = relax
                    self._incumbent_parent = -1
                    self._new_integer_solution = True
                    opt = np.zeros(numVars)
                    for i in FREE_VARIABLES:
                        opt[i] = self.sol[FREE_VARIABLES[i]]
                    for i in branch_var_set:
                        opt[i] = branch_var_set[i]
                    print "New best solution found, objective: %s" %relax
                elif integer_solution:
                    print "New integer solution found, objective: %s" %relax
                else:
                    print "Fractional solution (free variables):"
                for i in FREE_VARIABLES:
                    if self.sol[FREE_VARIABLES[i]] > 0:
                        print "x_%s = %s" %(i, self.sol[FREE_VARIABLES[i]])
                #For complete enumeration
                if complete_enumeration:
                    if self.SENSE[1] == 'Max':
                        relax = self._incumbent_value - 1
                    else:
                        relax = self._incumbent_value + 1
            if integer_solution:
                print "Integer solution"
                BBstatus = 'S'
                status = 'integer'
                color = 'lightblue'
            elif infeasible:
                print "Infeasible node"
                BBstatus = 'I'
                status = 'infeasible'
                color = 'orange'
            elif (not complete_enumeration and 
                  self._incumbent_value is not None and 
                  ((self.SENSE[0] == 'Max' and relax <= self._incumbent_value - etol) or
                   (self.SENSE[0] == 'Min' and relax >= self._incumbent_value + etol))):
                if self.SENSE[0] == 'Max':
                    print "Node pruned by bound (obj: %s, LB: %s)" %(relax,
                                                                 str(self._incumbent_value))
                else:
                    print "Node pruned by bound (obj: %s, UB: %s)" %(relax,
                                                                 str(self._incumbent_value))
                BBstatus = 'P'
                status = 'fathomed'
                color = 'red'
            elif cur_depth >= numVars :
                print "Reached a leaf"
                BBstatus = 'fathomed'
                status = 'L'
            else:
                BBstatus = 'C'
                status = 'candidate'
                color = 'yellow'
            if BBstatus is 'I':
                if self.get_layout() == 'dot2tex':
                    label = '\text{I}'
                else:
                    label = 'I'
            else:
                label = "%.1f"%relax
                    
            #====================================
            # Branch
            #====================================

            if BBstatus is 'C':
                branch_var_list, found_ISC = self.Branch(FREE_VARIABLES, OBJ_OFFSET, debug_print)
                label = label + "\n" + str(branch_var_list)
                if branch_var_list == []:
                    print "Node pruned because of empty cover!"
                    BBstatus = 'P'
                    status = 'fathomed'
                    color = 'red'

            #====================================
            # Update Tree
            #====================================
            
            if iter_count == 0:
                if status is 'fathomed':
                    if self._incumbent_value is None:
                        print 'WARNING: Encountered "fathom" line before '+\
                            'first incumbent.'
#                self.AddOrUpdateNode(0, DUMMY_NODE, None, 'candidate', relax,
#                                 integer_infeasibility_count,
#                                 integer_infeasibility_sum,
#                                 label = label,
#                                 obj = relax, color = color,
#                                 style = 'filled', fillcolor = color)
                self.add_root(0, status = status, label = label, obj = relax, 
                              color = color, style = 'filled', fillcolor = color)
            else:
                if status is 'infeasible':
                    relax = self.get_node_attr(parent, 'lp_bound')
                elif status is 'fathomed':
                    if self._incumbent_value is None:
                        print 'WARNING: Encountered "fathom" line before'+\
                            ' first incumbent.'
                        print '  This may indicate an error in the input file.'
#                self.AddOrUpdateNode(cur_index, parent, _direction[sense],
#                                     status, relax,
#                                     integer_infeasibility_count,
#                                     integer_infeasibility_sum,
#                                     branch_var = branch_var,
#                                     branch_var_value = var_values[branch_var],
#                                     sense = sense, rhs = rhs, obj = relax,
#                                     color = color, style = 'filled',
#                                     label = label, fillcolor = color)
                self.add_child(cur_index, parent, status = status,
                               branch_var_set = branch_var_set, obj = relax,
                               color = color, style = 'filled',
                               label = label, fillcolor = color)
            if BBstatus is 'C':
                self.CreateNewNodes(branch_var_list, found_ISC, cur_index)
                #self.set_node_attr(cur_index, 'fillcolor', 'green')

            if iter_count is not 0:
                if var_set_to_one is not -1:
                    self.set_edge_attr(parent, cur_index, 'label',
                                       str(var_set_to_one) + "=1")
                else:
                    self.set_edge_attr(parent, cur_index, 'label',
                                       str(var_set_to_zero) + "=0")
            iter_count += 1

            #====================================
            # Display Tree
            #====================================
           
            if self.root is not None and display_interval is not None and\
                    iter_count%display_interval == 0:
                self.display(count=iter_count)

        #====================================
        # Print Final Results
        #====================================
            
        timer = int(math.ceil((time.time()-timer)*1000))
        print ""
        print "==========================================="
        print "Branch and bound completed in %sms" %timer
        print "Strategy: %s" %self.branch_strategy
        if complete_enumeration:
            print "Complete enumeration"
        print "%s nodes visited " %self.real_node_count
        print "%s LP's solved" %lp_count
        print "==========================================="
        #print optimal solution
        if self.attr['display'] is not 'off':
            self.display()
        self._lp_count = lp_count
        if self._incumbent_value:
            if opt == None:
                print "No improving solution found"
            else:
                print "Optimal solution"
                for (i, val) in enumerate(opt):
                    if val > 0:
                        print "x_%s = %s" %(i, val)
                print "Objective function value"
                print "==========================================="
                print self._incumbent_value
            return opt, self._incumbent_value, self.real_node_count
        else:
            print "Problem infeasible"
            print "==========================================="
            return None, None, self.real_node_count

    def Branch(self, FREE_VARIABLES , OBJ_OFFSET, debug_print):
        # Choose a branching set
        found_ISC = False
        sense = self.SENSE[1]
        if (self.branch_strategy == INTERDICTION_BRANCHING and self._incumbent_value is not None):
            M = 100000
            BRANCH_VARIABLES = {}
            NO_BRANCH_VARIABLES = {}
            if self.branch_on_fractional:
                j, k = 0, 0
                for i in FREE_VARIABLES:
                    if isInt(self.sol[FREE_VARIABLES[i]]):
                        NO_BRANCH_VARIABLES[i] = j
                        j += 1 
                    else:
                        BRANCH_VARIABLES[i] = k
                        k += 1
            else:
                j = 0
                for i in FREE_VARIABLES:
                    BRANCH_VARIABLES[i] = j
                    j += 1
            interdict_prob = CyLPModel()
            y = interdict_prob.addVariable('y', len(BRANCH_VARIABLES), isInt = True) #binary
            u = interdict_prob.addVariable('u', len(sense))
            w = interdict_prob.addVariable('w', len(FREE_VARIABLES))
            interdict_prob.objective = y.sum()
            if self.SENSE[0] == 'Max':
                interdict_prob += CyLPArray(self.ADJ_RHS)*u + w.sum() <= self._incumbent_value - OBJ_OFFSET
                k = 0
                for i in FREE_VARIABLES:
                    try:
                        interdict_prob += self.MAT.getcol(i).transpose()*u + w[FREE_VARIABLES[i]] + M*y[BRANCH_VARIABLES[i]] >= self.OBJ[i]
                    except:
                        interdict_prob += self.MAT.getcol(i).transpose()*u + w[FREE_VARIABLES[i]] >= self.OBJ[i]
            else: 
                interdict_prob += CyLPArray(self.ADJ_RHS)*u + w.sum() >= self._incumbent_value - OBJ_OFFSET 
                k = 0
                for i in FREE_VARIABLES:
                    try:
                        interdict_prob += self.MAT.getcol(i).transpose()*u + w[FREE_VARIABLES[i]] - M*y[BRANCH_VARIABLES[i]] <= self.OBJ[i]
                    except:
                        interdict_prob += self.MAT.getcol(i).transpose()*u + w[FREE_VARIABLES[i]] <= self.OBJ[i]
            for (i, j) in enumerate(sense):
                if (self.SENSE[0] == 'Max' and j == '<=' or self.SENSE[0] == 'Min' and j == '>='):
                    interdict_prob += u[i] >= 0
                elif j != '=':
                    interdict_prob += u[i] <= 0
            if (self.SENSE[0] == 'Max'):
                interdict_prob += w >= 0
            else:
                interdict_prob += w <= 0                
            interdict_prob += 0 <= y <= np.ones(len(BRANCH_VARIABLES))
            lp = CyClpSimplex(interdict_prob)
            lp.writeMps('interdict.mps')
            cbcModel = lp.getCbcModel()
            #cbcModel.logLevel = 0
            cbcModel.maximumSeconds = 100
            cbcModel.solve()
            if cbcModel.status == 'solution' or cbcModel.status == 'stopped on time':
                if debug_print:
                    print "Cons Dual Vars:", cbcModel.primalVariableSolution['u']
                    print "Bound Dual Vars:", cbcModel.primalVariableSolution['w']
                    print "Interdiction Vars:", cbcModel.primalVariableSolution['y']
                    print "Value of all zeros solution:",
                    print np.dot(cbcModel.primalVariableSolution['u'], self.ADJ_RHS) + cbcModel.primalVariableSolution['w'].sum() + OBJ_OFFSET
                branch_var_list = [i for i in BRANCH_VARIABLES if cbcModel.primalVariableSolution['y'][BRANCH_VARIABLES[i]] > 0.5]
                found_ISC = True
        if found_ISC is False:
            #most fractional variable
            if self.branch_strategy is INTERDICTION_BRANCHING:
                print "Falling back to fractional branching"
            branch_var = int(np.argmax(np.abs(np.around(self.sol)-self.sol)))
            if etol < self.sol[branch_var] < 1 - etol:
                branch_var_list = [branch_var]
        print "Branching on set:"
        print branch_var_list
        
        return branch_var_list, found_ISC
    
    def CreateNewNodes(self, branch_var_list, found_ISC, parent):
        #Create new nodes
        depth = self.get_node_attr(parent, 'level') + 1
        bound = self.get_node_attr(parent, 'obj')
        if self.search_strategy is DEPTH_FIRST:
            priority = -depth
        elif self.search_strategy is BEST_FIRST:
            priority = -bound
        for i in range(len(branch_var_list)):
            branch_var_set = {}
            branch_var_set[branch_var_list[i]] = 1
            for j in range(i):
                branch_var_set[branch_var_list[j]] = 0
            self.Q.push(self.node_count, priority, (self.node_count, parent, bound, branch_var_set))
            self.node_count += 1
            self.real_node_count += 1
        if found_ISC is False:
            # This is the all-zeros branch that we discard in the interdiction case
            branch_var_set = {}
            for i in branch_var_list:
                branch_var_set[i] = 0
            self.Q.push(self.node_count, priority, (self.node_count, parent, bound, branch_var_set))
            self.node_count += 1
            self.real_node_count += 1
        if found_ISC is True and len(branch_var_set) == 1:
            self.real_node_count -= 1
            
def isInt(x):
    '''
    Return True if x is an integer, or if x is a numpy array
    with all integer elements, False otherwise
    '''
    if isinstance(x, (int, long, float)):
        return abs(math.floor(x) - x) < 1e-6
    return (np.abs(np.around(x) - x) < 1e-6).all()

def read_instance(module_name = None, file_name = None):

    if module_name is not None:
        mip = ilib.import_module(module_name)
        return np.matrix(mip.A), np.ndarray(mip.b), mip.c, mip.sense, mip.integerIndices
    elif file_name is not None:
        m = CyClpSimplex()
        m.readMps(file_name)
        mat = m.matrix
        A = sparse.csc_matrix((mat.elements, mat.indices, mat.vectorStarts),
                              shape=(m.nConstraints, m.nVariables)).tocsr()
        integerIndices = [i for (i, j) in enumerate(m.integerInformation) if j == True]
        INFINITY = m.getCoinInfinity()
        sense = []
        b = []
        for i in range(m.nConstraints):
            if m.constraintsLower[i] > -INFINITY:
                if m.constraintsUpper[i] >= INFINITY:
                    sense.append('>=')
                elif m.constraintsLower[i] == m.constraintsUpper[i]:
                    sense.append('=')
                else:
                    print "Function does not support ranged constraint..."
                b.append(m.constraintsLower[i])
            elif m.constraintsUpper[i] < INFINITY:
                sense.append('>=')
                b.append(-m.constraintsUpper[i])
                for idx in range(A.indptr[i], A.indptr[i+1]):
                    A.data[idx] = -A.data[idx]
            else:
                print "Error: Free constraint..."
                break
        return A.tocsc(), b, m.objectiveCoefficients, sense, integerIndices
    else:
        print "No file or module name specified..."
        return None, None, None, None, None, None
    
if __name__ == '__main__':
    generate_instance = False

    T = InterdictionTree()
    T.set_display_mode('off')
    T.branch_strategy = INTERDICTION_BRANCHING
    #T.branch_strategy = MOST_FRACTIONAL
    
    if generate_instance:
        numV = 40
        numC = 20
        VARS = range(numV)
        CONS = ["C"+str(i) for i in range(numC)]

        #Generate random MILP
        T.GenerateRandomMILP(VARS, CONS, rand_seed = 2)
        #T.branch_on_fractional = False
    else:
        path = 'C:\\cygwin64\\home\\ted\\Data\\miplib2010-1.0.4\\instances\\miplib2010\\'
        #T.MAT, T.RHS, T.OBJ, sense, T.IntegerIndices = read_instance(file_name = path + 'acc-tight5.mps')
        #T._incumbent_value = 1
        #T.MAT, T.RHS, T.OBJ, sense, T.IntegerIndices = read_instance(file_name = path + 'eilB101.mps')
        #T._incumbent_value = 1218
        #T.MAT, T.RHS, T.OBJ, sense, T.IntegerIndices = read_instance(file_name = path + 'eil33-2.mps')
        #T._incumbent_value = 935
        T.MAT, T.RHS, T.OBJ, sense, T.IntegerIndices = read_instance(file_name = path + 'cov1075.mps')
        T._incumbent_value = 20
        #T.MAT, T.RHS, T.OBJ, sense, T.IntegerIndices = read_instance(file_name = 'p0033.mps')
        #T._incumbent_value = 3090
        #T.MAT, T.RHS, T.OBJ, sense, T.IntegerIndices = read_instance(file_name = path + 'iis-bupa-cov.mps')
        #T._incumbent_value = 36
        T.SENSE = ('Min', sense)
        
    T.BranchAndBound(max_iter_num = 1, debug_print = True)
'''
    numV = 40
    numC = 20
    VARS = dict((i, 0) for i in range(numV))
    CONS = ["C"+str(i) for i in range(numC)]
    opt = []
    nodes = []
    for i in range(10):
        T = InterdictionTree()
        T.set_display_mode('off')
        #Generate random MILP
        T.GenerateRandomMILP(VARS, CONS, rand_seed = i)
        T.branch_strategy = MOST_FRACTIONAL
        #T.incumbent_value = 218
        sol, solval, node_nobound_frac = T.BranchAndBound()
        opt.append(solval)
        
        T = InterdictionTree()
        T.set_display_mode('off')
        #Generate random MILP
        T.GenerateRandomMILP(VARS, CONS, rand_seed = i)
        T.branch_strategy = MOST_FRACTIONAL
        T.incumbent_value = opt[i]
        solval, sol, node_bound_frac = T.BranchAndBound()
        
        T = InterdictionTree()
        T.set_display_mode('off')
        #Generate random MILP
        T.GenerateRandomMILP(VARS, CONS, rand_seed = i)
        T.branch_strategy = INTERDICTION_BRANCHING
        T.branch_on_fractional = True
        T.incumbent_value = opt[i]
        solval, sol, node_bound_interdict = T.BranchAndBound()
        
        nodes.append((node_nobound_frac, node_bound_frac, node_bound_interdict))

    print nodes
'''