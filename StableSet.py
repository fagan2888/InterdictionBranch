from InterdictionBB import InterdictionTree, MOST_FRACTIONAL, INTERDICTION_BRANCHING

try:
    from src.gimpy import Graph, UNDIRECTED_GRAPH
except ImportError:
    from coinor.gimpy import Graph

from pulp import LpVariable, lpSum, LpProblem, LpMaximize, LpMinimize, LpConstraint
from pulp import LpStatus, value, LpBinary

node_counts = {}
numNodes = 30
numSeeds = 10
display = 'off'
for b_rule in [MOST_FRACTIONAL, INTERDICTION_BRANCHING]:
    for seed in range(numSeeds):
        G = Graph(type = UNDIRECTED_GRAPH, splines = 'true', K = 1.5)
        G.random(numnodes = numNodes, density = 0.5, length_range = None, seedInput = seed)
        G.set_display_mode('off')

        nodes = G.get_node_list()

        T = InterdictionTree()
        T.set_display_mode(display)
        #Simple Heuristic
        IS = [-1 for i in nodes]
        for i in nodes:
            if IS[i] == -1:
                IS[i] = 1
                for j in G.get_neighbors(i):
                    IS[j] = 0
        
        T._incumbent_value = sum(IS)
        print 'Heuristic solution value: ', T._incumbent_value

        T.VARIABLES = []
        T.CONSTRAINTS = []
        T.OBJ = {}
        T.RHS = {}
        T.MAT = {}
        T.branch_on_fractional = True
        T.branch_strategy = b_rule
        for i in nodes:
            T.VARIABLES.append(i)
            T.OBJ[i] = 1
            for j in nodes:
                if G.check_edge(i, j):
                    constraint_label = 'C_'+str(i)+'_'+str(j)
                    T.CONSTRAINTS.append(constraint_label)
                    for k in nodes:
                        T.MAT.update([((constraint_label, k), 0) for k in nodes])
                    T.MAT[(constraint_label, i)] = 1
                    T.MAT[(constraint_label, j)] = 1
                    T.RHS[constraint_label] = 1

        opt, optval, node_count = T.BranchAndBound()

        for i in opt:
            if opt[i] >= 0.5:
                G.set_node_attr(i, 'style', 'filled')
                G.set_node_attr(i, 'fillcolor', 'red')
                G.set_node_attr(i, 'fontcolor', 'white')

        #G.display()
        node_counts[(seed, b_rule)] = node_count

for seed in range(numSeeds):
    print node_counts[seed, MOST_FRACTIONAL], node_counts[seed, INTERDICTION_BRANCHING]

