import math
import random
import sys
try:
    from src.gimpy import Tree
except ImportError:
    from coinor.gimpy import Tree
import time
try:
    from src.blimpy import PriorityQueue
except ImportError:
    from coinor.blimpy import PriorityQueue
#from pygame.transform import scale
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
# branch strategy
BRANCH_STRATEGY = None
# search strategy
SEARCH_STRATEGY = None
# branching strategies
MOST_FRACTIONAL = 'Most Fraction'
INTERDICTION_BRANCHING = 'Interdiction Branching'
# search strategies
DEPTH_FIRST = 'Depth First'
BEST_FIRST = 'Best First'
BEST_ESTIMATE = 'Best Estimate'
INFINITY = sys.maxint

DOT2TEX_TEMPLATE = r'''
\documentclass[landscape]{article}
\usepackage[x11names, rgb]{xcolor}
\usepackage[<<textencoding>>]{inputenc}
\usepackage{tikz}
\usetikzlibrary{snakes,arrows,shapes}
\usepackage{amsmath}
\usepackage[margin=2cm,nohead]{geometry}%
<<startpreprocsection>>%
\usepackage[active,auctex]{preview}
<<endpreprocsection>>%
<<gvcols>>%
<<cropcode>>%
<<docpreamble>>%

\begin{document}
\pagestyle{empty}
%
<<startpreprocsection>>%
<<preproccode>>
<<endpreprocsection>>%
%
<<startoutputsection>>
\enlargethispage{100cm}
% Start of code
% \begin{tikzpicture}[anchor=mid,>=latex',join=bevel,<<graphstyle>>]
\resizebox{\textwidth}{!}{
\begin{tikzpicture}[>=latex',join=bevel,<<graphstyle>>]
\pgfsetlinewidth{1bp}
<<figpreamble>>%
<<drawcommands>>
<<figpostamble>>%
\end{tikzpicture}
% End of code
}
<<endoutputsection>>
%
\end{document}
%
<<startfigonlysection>>
\begin{tikzpicture}[>=latex,join=bevel,<<graphstyle>>]
\pgfsetlinewidth{1bp}
<<figpreamble>>%
<<drawcommands>>
<<figpostamble>>%
\end{tikzpicture}
<<endfigonlysection>>
'''

class InterdictionTree(Tree):
    
    def __init__(self, **attrs):
        Tree.__init__(self, **attrs)
        self._incumbent_value = None

    def GenerateRandomMILP(self, VARIABLES, CONSTRAINTS, density = 0.2,
                           maxObjCoeff = 10, maxConsCoeff = 10, 
                           tightness = 2, rand_seed = 2):
        random.seed(rand_seed)
        OBJ = dict((i, random.randint(1, maxObjCoeff)) for i in VARIABLES)
        MAT = dict(((i, j), random.randint(1, maxConsCoeff) 
                        if random.random() <= density else 0)
                for i in CONSTRAINTS for j in VARIABLES)
        RHS = dict((i, random.randint(int(len(VARIABLES)*density*maxConsCoeff/tightness),
                                  int(len(VARIABLES)*density*maxConsCoeff/1.5)))
                                  for i in CONSTRAINTS)
        return OBJ, MAT, RHS
    
    def BranchAndBound(self, VARIABLES, CONSTRAINTS, OBJ, MAT, RHS,
                       branch_strategy = INTERDICTION_BRANCHING,
                       search_strategy = BEST_FIRST,
                       complete_enumeration = False,
                       display_interval = None, LB = 0, 
                       debug_print = False):
        if self.get_layout() == 'dot2tex':
            cluster_attrs = {'name':'Key', 'label':r'\text{Key}', 'fontsize':'12'}
            self.add_node('C', label = r'\text{Candidate}', style = 'filled',
                          color = 'yellow', fillcolor = 'yellow')
            self.add_node('I', label = r'\text{Infeasible}', style = 'filled',
                          color = 'orange', fillcolor = 'orange')
            self.add_node('S', label = r'\text{Solution}', style = 'filled',
                          color = 'lightblue', fillcolor = 'lightblue')
            self.add_node('P', label = r'\text{Pruned}', style = 'filled',
                          color = 'red', fillcolor = 'red')
            self.add_node('PC', label = r'\text{Pruned}$\\ $\text{Candidate}', style = 'filled',
                          color = 'red', fillcolor = 'yellow')
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
        # The number of LP's solved, and the number of nodes solved
        node_count = 1
        iter_count = 0
        lp_count = 0
        var   = LpVariable.dicts("", VARIABLES, 0, 1)
        numVars = len(VARIABLES)
        # List of incumbent solution variable values
        opt = dict([(i, 0) for i in VARIABLES])
        print "==========================================="
        print "Starting Branch and Bound"
        if branch_strategy is MOST_FRACTIONAL:
            print "Most fractional variable"
        elif branch_strategy is INTERDICTION_BRANCHING:
            print "Interdiction branching"
        else:
            print "Unknown branching strategy %s" %branch_strategy
        if search_strategy is DEPTH_FIRST:
            print "Depth first search strategy"
        elif search_strategy is BEST_FIRST:
            print "Best first search strategy"
        else:
            print "Unknown search strategy %s" %search_strategy
        print "==========================================="
        # List of candidate nodes
        Q = PriorityQueue()
        # The current tree depth
        cur_depth = 0
        cur_index = 0
        # Timer
        timer = time.time()
        Q.push(0, (0, None, None, None), 0)
        # Branch and Bound Loop
        while not Q.isEmpty():
            infeasible = False
            integer_solution = False
            cur_index, parent, relax, branch_vars = Q.pop()
            if cur_index is not 0:
                cur_depth = self.get_node_attr(parent, 'level') + 1
            else:
                cur_depth = 0
            print ""
            print "----------------------------------------------------"
            print ""
            print "Node: %s, Depth: %s, LB: %s" %(cur_index,cur_depth,LB)
            if relax is not None and relax <= LB + 1:
                print "Node pruned immediately by bound"
                self.set_node_attr(parent, 'color', 'red')
                continue
            #====================================
            #    LP Relaxation
            #====================================
            # Fix all prescribed variables
            branch_var_set = {}
            if cur_index is not 0:
                branch_var_set.update(branch_vars)
                pred = parent
                while str(pred) is not '0':
                    pred_branch_var_set = self.get_node_attr(pred, 'branch_var_set')
                    branch_var_set.update(pred_branch_var_set)
                    pred = self.get_node_attr(pred, 'parent')
            print "Branching variables set:"
            print branch_var_set
            # Compute lower bound by LP relaxation
            ADJ_RHS = dict((i, RHS[i]) for i in CONSTRAINTS)
            for j in branch_var_set:
                if branch_var_set[j] == 1:
                    for i in CONSTRAINTS:
                        ADJ_RHS[i] -= MAT[i, j]
            FREE_VARIABLES = [i for i in VARIABLES if i not in branch_var_set]
            OBJ_OFFSET = 0
            for j in branch_var_set:
                if branch_var_set[j] == 1:
                    OBJ_OFFSET += OBJ[j]
            print OBJ_OFFSET 
            if FREE_VARIABLES != []:
                prob = LpProblem("relax", LpMaximize)
                prob += lpSum([OBJ[j]*var[j] for j in FREE_VARIABLES]), "Objective"
                for i in CONSTRAINTS:
                    prob += lpSum([MAT[i, j]*var[j] for j in FREE_VARIABLES]) <= ADJ_RHS[i], i
                # Solve the LP relaxation
                prob.solve()
                lp_count = lp_count +1
                # Check infeasibility
                infeasible = LpStatus[prob.status] == "Infeasible" or \
                    LpStatus[prob.status] == "Undefined"
                if debug_print:
                    print "Duals on constraints in LP relaxation:"
                    for i in CONSTRAINTS:
                        print i, prob.constraints[i].pi
                    print "Reduced costs on variables in LP relaxation:"
                    for j in FREE_VARIABLES:
                        print j, var[j].dj
                    print "Dual solution value:",
                    print value(lpSum(prob.constraints[i].pi*ADJ_RHS[i] for i in CONSTRAINTS 
                                      if prob.constraints[i].pi is not None) +
                                lpSum(var[j].dj for j in FREE_VARIABLES if var[j].dj > .00001) +
                                OBJ_OFFSET)
                if not infeasible:
                    relax = value(prob.objective) + OBJ_OFFSET
            else:
                print "All variables fixed...no LP to solve" 
                infeasible = False
                for i in CONSTRAINTS:
                    if ADJ_RHS[i] < 0:
                        infeasible = True
                        break
                if not infeasible:
                    relax = OBJ_OFFSET
            # Print status
            if infeasible:
                print "Node status: infeasible"
                relax = 0
            else:
                print "Node status: feasible with obj = %s", relax
                var_values = dict([(i, var[i].varValue) for i in FREE_VARIABLES])
                integer_solution = True
                for i in FREE_VARIABLES:
                    if (var_values[i] not in set([0,1])):
                        integer_solution = False
                        break
                if (integer_solution and relax > LB):
                    LB = relax
                    opt = dict([(i, 0) for i in VARIABLES])
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
                elif (integer_solution and relax<=LB):
                    print "New integer solution found, objective: %s" %relax
                    for i in FREE_VARIABLES:
                        if var_values[i] > 0:
                            print "%s = %s" %(i, var_values[i])
                else:
                    print "Fractional solution:"
                    for i in FREE_VARIABLES:
                        if var_values[i] > 0:
                            print "%s = %s" %(i, var_values[i])
                #For complete enumeration
                if complete_enumeration:
                    relax = LB - 1
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
            elif not complete_enumeration and relax <= LB + 0.99:
                print "Node pruned by bound (obj: %s, LB: %s)" %(relax,LB)
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
            if iter_count == 0:
                if status is 'fathomed':
                    if self._incumbent_value is None:
                        print 'WARNING: Encountered "fathom" line before '+\
                            'first incumbent.'
                self.add_root(0, status = status, label = label, obj = relax, 
                              color = color, style = 'filled', fillcolor = color)
                if status is 'integer':
                    self._incumbent_value = relax
                    self._incumbent_parent = -1
                    self._new_integer_solution = True
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
                self.add_child(cur_index, parent, status = status,
                               branch_var_set = branch_var_set, obj = relax,
                               color = color, style = 'filled',
                               label = label, fillcolor = color)
                if status is 'integer':
                    self._incumbent_value = relax
                    self._incumbent_parent = parent
                    self._new_integer_solution = True
                if ETREE_INSTALLED and self.attr['display'] == 'svg':
                    self.write_as_svg(filename = "node%d" % iter_count,
                                      prevfile = "node%d" % (iter_count - 1),
                                      nextfile = "node%d" % (iter_count + 1),
                                      highlight = cur_index)
            iter_count += 1
            if BBstatus == 'C':
                # Branching:
                # Choose a branching set
                found_ISC = False
                if branch_strategy is INTERDICTION_BRANCHING and LB > 0:
                    M = 100
                    interdict_prob = LpProblem("interdict", LpMinimize)
                    interdict_vars = LpVariable.dicts("y", FREE_VARIABLES, 0, 1, LpBinary)
                    cons_dual_vars = LpVariable.dicts("u", CONSTRAINTS, 0)
                    bound_dual_vars = LpVariable.dicts("w", FREE_VARIABLES, 0)
                    interdict_prob += lpSum(interdict_vars[i] for i in FREE_VARIABLES), "Objective"
                    interdict_prob += (lpSum(cons_dual_vars[i]*ADJ_RHS[i] for i in CONSTRAINTS) 
                       + lpSum(bound_dual_vars[j] for j in FREE_VARIABLES) <= LB - OBJ_OFFSET - 1, "Bound")
                    for j in FREE_VARIABLES:
                        interdict_prob += (lpSum(cons_dual_vars[i]*MAT[i, j] for i in CONSTRAINTS) 
                           + bound_dual_vars[j] >= OBJ[j] - M*interdict_vars[j])
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
                            print value(lpSum(cons_dual_vars[i]*ADJ_RHS[i] for i in CONSTRAINTS) 
                                    + lpSum(bound_dual_vars[j] for j in FREE_VARIABLES) + OBJ_OFFSET)
                        branch_var_list = [i for i in interdict_vars if interdict_vars[i].varValue > 0.5]
                        found_ISC = True
                if found_ISC is False:
                    #most fractional variable
                    print "Falling back to fractional branching"
                    min_frac = -1
                    for i in FREE_VARIABLES:
                        frac = min(var[i].varValue-math.floor(var[i].varValue),
                                   math.ceil(var[i].varValue)- var[i].varValue)
                        if (frac> min_frac):
                            min_frac = frac
                            branch_var_list = [i]
                print "Branching on set:"
                print branch_var_list
                #Create new nodes
                if search_strategy is DEPTH_FIRST:
                    priority = -cur_depth - 1
                elif search_strategy is BEST_FIRST:
                    priority = -relax
                for i in range(len(branch_var_list)):
                    branch_var_set = {}
                    branch_var_set[branch_var_list[i]] = 1
                    for j in range(i):
                        branch_var_set[branch_var_list[j]] = 0
                    Q.push(node_count, (node_count, cur_index, relax, branch_var_set), priority)
                    node_count += 1
                if found_ISC is False:
                    # This is the all-zeros branch that we discard in the interdiction case
                    branch_var_set = {}
                    for i in branch_var_list:
                        branch_var_set[i] = 0
                    Q.push(node_count, (node_count, cur_index, relax, branch_var_set), priority)
                    node_count += 1
                self.set_node_attr(cur_index, color, 'green')
            if self.root is not None and display_interval is not None and\
                    iter_count%display_interval == 0:
                self.display(count=iter_count)

        timer = int(math.ceil((time.time()-timer)*1000))
        print ""
        print "==========================================="
        print "Branch and bound completed in %sms" %timer
        print "Strategy: %s" %branch_strategy
        if complete_enumeration:
            print "Complete enumeration"
        print "%s nodes visited " %node_count
        print "%s LP's solved" %lp_count
        print "==========================================="
        print "Optimal solution"
        #print optimal solution
        for i in sorted(VARIABLES):
            if opt[i] > 0:
                print "%s = %s" %(i, opt[i])
        print "Objective function value"
        print LB
        print "==========================================="
        if self.attr['display'] is not 'off':
            self.display()
        self._lp_count = lp_count
        return opt, LB
    
if __name__ == '__main__':
    T = InterdictionTree()
    T.set_display_mode('xdot')

    numVars = 40
    numCons = 20
    VARIABLES = dict((i, 0) for i in range(numVars))
    CONSTRAINTS = ["C"+str(i) for i in range(numCons)]

    #Generate random MILP
    OBJ, MAT, RHS = T.GenerateRandomMILP(VARIABLES, CONSTRAINTS)

    T.BranchAndBound(VARIABLES, CONSTRAINTS, OBJ, MAT, RHS)
            