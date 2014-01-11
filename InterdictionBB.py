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
from pulp import LpVariable, lpSum, LpProblem, LpMaximize, LpMinimize, LpConstraint
from pulp import LpStatus, value, LpBinary

try:
    import pygame # for locals.QUIT, locals.KEYDOWN,display,image,event,init
except ImportError:
    PYGAME_INSTALLED = False
else:
    PYGAME_INSTALLED = True

try:
    import dot2tex # for dot2tex method
except ImportError:
    DOT2TEX_INSTALLED = False
else:
    DOT2TEX_INSTALLED = True

try:
    from PIL import Image as PIL_Image
except ImportError:
    PIL_INSTALLED = False
else:
    PIL_INSTALLED = True

try:
    import pygtk
    import gtk
    import xdot
except ImportError:
    XDOT_INSTALLED = False
else:
    XDOT_INSTALLED = True

try:
    import lxml # for etree
except ImportError:
    ETREE_INSTALLED = False
else:
    ETREE_INSTALLED = True

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
                       display_interval = None, debug_print = False):

        #====================================
        # Initialize
        #====================================
        
        # The number of LP's solved, and the number of nodes solved
        self.node_count = 1
        self.real_node_count = 1
        iter_count = 0
        lp_count = 0
        self.var   = LpVariable.dicts("", self.VARIABLES, 0, 1)
        numVars = len(self.VARIABLES)
        # List of incumbent solution variable values
        opt = dict([(i, 0) for i in self.VARIABLES])
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
        self.Q.push(0, (0, None, None, None), 0)

        #====================================
        # Main Loop
        #====================================

        while not self.Q.isEmpty():

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
            print "Node: %s, Depth: %s, LB: %s" %(cur_index, cur_depth,
                                                  self._incumbent_value)
            if (relax is not None and self._incumbent_value is not None and
                relax <= self._incumbent_value + 1 - etol):
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
            self.ADJ_RHS = dict((i, self.RHS[i]) for i in self.CONSTRAINTS)
            for j in branch_var_set:
                if branch_var_set[j] == 1:
                    for i in self.CONSTRAINTS:
                        self.ADJ_RHS[i] -= self.MAT[i, j]
            FREE_VARIABLES = [i for i in self.VARIABLES if i not in branch_var_set]
            OBJ_OFFSET = 0
            for j in branch_var_set:
                if branch_var_set[j] == 1:
                    OBJ_OFFSET += self.OBJ[j]
            if debug_print: 
                print 'Objective offset: ', OBJ_OFFSET 
            if FREE_VARIABLES != []:
                self.LpRelaxation = LpProblem("relax", LpMaximize)
                self.LpRelaxation += lpSum([self.OBJ[j]*self.var[j] for j in FREE_VARIABLES]), "Objective"
                for i in self.CONSTRAINTS:
                    self.LpRelaxation += lpSum([self.MAT[i, j]*self.var[j] for j in FREE_VARIABLES]) <= self.ADJ_RHS[i], i
                # Solve the LP relaxation
                status = self.LpRelaxation.solve()
                lp_count = lp_count +1
                # Check infeasibility
                infeasible = LpStatus[status] == "Infeasible" or \
                    LpStatus[status] == "Undefined"
                if debug_print:
                    print "Duals on constraints in LP relaxation:"
                    for i in self.CONSTRAINTS:
                        print i, self.LpRelaxation.constraints[i].pi
                    print "Reduced costs on variables in LP relaxation:"
                    for j in FREE_VARIABLES:
                        print j, self.var[j].dj
                    print "Dual solution value:",
                    print value(lpSum(self.LpRelaxation.constraints[i].pi*self.ADJ_RHS[i] 
                                      for i in self.CONSTRAINTS 
                                      if self.LpRelaxation.constraints[i].pi is not None) +
                                lpSum(self.var[j].dj for j in FREE_VARIABLES 
                                      if self.var[j].dj > .00001) +
                                OBJ_OFFSET)
                if not infeasible:
                    relax = value(self.LpRelaxation.objective) + OBJ_OFFSET
            else:
                print "All variables fixed...no LP to solve" 
                infeasible = False
                for i in self.CONSTRAINTS:
                    if self.ADJ_RHS[i] < 0:
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
                var_values = dict([(i, self.var[i].varValue) for i in FREE_VARIABLES])
                integer_solution = True
                for i in FREE_VARIABLES:
                    if (var_values[i] > etol and var_values[i] < 1 - etol):
                        integer_solution = False
                        break
                if (integer_solution and (self._incumbent_value is None or 
                    relax > self._incumbent_value)):
                    self._incumbent_value = relax
                    self._incumbent_parent = -1
                    self._new_integer_solution = True
                    opt = dict([(i, 0) for i in self.VARIABLES])
                    for i in FREE_VARIABLES:
                        # These two have different data structures first one
                        #list, second one dictionary
                        opt[i] = var_values[i]
                    for i in branch_var_set:
                        if branch_var_set[i] == 1:
                            opt[i] = 1
                    print "New best solution found, objective: %s" %relax
                    for i in FREE_VARIABLES:
                        if var_values[i] > 0:
                            print "%s = %s" %(i, var_values[i])
                elif integer_solution:
                    print "New integer solution found, objective: %s" %relax
                    for i in FREE_VARIABLES:
                        if var_values[i] > 0:
                            print "%s = %s" %(i, var_values[i])
                else:
                    print "Fractional solution (free variables):"
                    for i in FREE_VARIABLES:
                        if var_values[i] > 0:
                            print "%s = %s" %(i, var_values[i])
                #For complete enumeration
                if complete_enumeration:
                    relax = self._incumbent_value - 1
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
            elif (not complete_enumeration and self._incumbent_value is not None and 
                  relax <= self._incumbent_value + 1 - etol):
                print "Node pruned by bound (obj: %s, LB: %s)" %(relax,
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
                if ETREE_INSTALLED and self.attr['display'] == 'svg':
                    self.write_as_svg(filename = "node%d" % iter_count,
                                      nextfile = "node%d" % (iter_count + 1),
                                      highlight = cur_index)
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
                if ETREE_INSTALLED and self.attr['display'] == 'svg':
                    self.write_as_svg(filename = "node%d" % iter_count,
                                      prevfile = "node%d" % (iter_count - 1),
                                      nextfile = "node%d" % (iter_count + 1),
                                      highlight = cur_index)
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
        print "Optimal solution"
        #print optimal solution
        for i in sorted(self.VARIABLES):
            if opt[i] > 0:
                print "%s = %s" %(i, opt[i])
        print "Objective function value"
        print self._incumbent_value
        print "==========================================="
        if self.attr['display'] is not 'off':
            self.display()
        self._lp_count = lp_count
        return opt, self._incumbent_value, self.real_node_count

    def Branch(self, FREE_VARIABLES , OBJ_OFFSET, debug_print):
        # Choose a branching set
        found_ISC = False
        if (self.branch_strategy is INTERDICTION_BRANCHING and self._incumbent_value is not None and
            self._incumbent_value > 0):
            M = 100
            if self.branch_on_fractional:
                BRANCH_VARIABLES = [i for i in FREE_VARIABLES if (self.var[i].varValue > etol and
                                                                  self.var[i].varValue < 1-etol)]
                NO_BRANCH_VARIABLES = [i for i in FREE_VARIABLES if (self.var[i].varValue < etol or
                                                                     self.var[i].varValue > 1-etol)]
            else:
                BRANCH_VARIABLES = FREE_VARIABLES
                NO_BRANCH_VARIABLES = [] 
            interdict_prob = LpProblem("interdict", LpMinimize)
            interdict_vars = LpVariable.dicts("y", BRANCH_VARIABLES , 0, 1, LpBinary)
            cons_dual_vars = LpVariable.dicts("u", self.CONSTRAINTS, 0)
            bound_dual_vars = LpVariable.dicts("w", FREE_VARIABLES , 0)
            interdict_prob += lpSum(interdict_vars[i] for i in BRANCH_VARIABLES ), "Objective"
            interdict_prob += (lpSum(cons_dual_vars[i]*self.ADJ_RHS[i] for i in self.CONSTRAINTS) 
                               + lpSum(bound_dual_vars[j] for j in FREE_VARIABLES ) <= self._incumbent_value - OBJ_OFFSET - 1, "Bound")
            for j in BRANCH_VARIABLES:
                try:
                    interdict_prob += (lpSum(cons_dual_vars[i]*self.MAT[i, j] for i in self.CONSTRAINTS) 
                                   + bound_dual_vars[j] >= self.OBJ[j] - M*interdict_vars[j])
                except:
                    pass
            for j in NO_BRANCH_VARIABLES:
                interdict_prob += (lpSum(cons_dual_vars[i]*self.MAT[i, j] for i in self.CONSTRAINTS) 
                                   + bound_dual_vars[j] >= self.OBJ[j])
            interdict_status = interdict_prob.solve()
            if LpStatus[interdict_status] == 'Optimal':
                if debug_print:
                    print "Cons Dual Vars:"
                    for i in cons_dual_vars:
                        print i, cons_dual_vars[i].varValue
                    print "Bound Dual Vars:"
                    for i in bound_dual_vars:
                        print i, bound_dual_vars[i].varValue
                    print "Interdiction Vars:"
                    for i in interdict_vars:
                        print i, interdict_vars[i].varValue
                    print "Value of all zeros solution:",
                    print value(lpSum(cons_dual_vars[i]*self.ADJ_RHS[i] for i in self.CONSTRAINTS) 
                                + lpSum(bound_dual_vars[j] for j in FREE_VARIABLES) + OBJ_OFFSET)
                branch_var_list = [i for i in interdict_vars if interdict_vars[i].varValue > 0.5]
                found_ISC = True
        if found_ISC is False:
            #most fractional variable
            if self.branch_strategy is INTERDICTION_BRANCHING:
                print "Falling back to fractional branching"
            min_frac = -1
            for i in FREE_VARIABLES:
                frac = min(self.var[i].varValue-math.floor(self.var[i].varValue),
                           math.ceil(self.var[i].varValue)- self.var[i].varValue)
                if (frac> min_frac):
                    min_frac = frac
                    branch_var_list = [i]
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
            self.Q.push(self.node_count, (self.node_count, parent, 
                                          bound, branch_var_set), priority)
            self.node_count += 1
            self.real_node_count += 1
        if found_ISC is False:
            # This is the all-zeros branch that we discard in the interdiction case
            branch_var_set = {}
            for i in branch_var_list:
                branch_var_set[i] = 0
            self.Q.push(self.node_count, (self.node_count, parent, 
                                          bound, branch_var_set), priority)
            self.node_count += 1
            self.real_node_count += 1
        if found_ISC is True and len(branch_var_set) == 1:
            self.real_node_count -= 1
            
    
if __name__ == '__main__':
#    '''
    T = InterdictionTree()
    T.set_display_mode('xdot')
    
    numV = 40
    numC = 20
    VARS = range(numV)
    CONS = ["C"+str(i) for i in range(numC)]

    #Generate random MILP
    T.GenerateRandomMILP(VARS, CONS, rand_seed = 2)
    #T.branch_on_fractional = False
    T.branch_strategy = MOST_FRACTIONAL
    #T.incumbent_value = 213
    T.BranchAndBound()
#    '''
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