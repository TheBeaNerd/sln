import graph
import cnf

# g = {1: set([9, 12]), 2: set([16, 10]), 3: set([14]), 4: set([11]), 5: set([13]), 6: set([15]), 7: set([-7, 28, 29, 7]), 8: set([24, 9, 18, 26]), 9: set([8, 1, 4]), 10: set([4, 2, -12]), 11: set([4, 3, 21]), 12: set([1, 10, 5, -10]), 13: set([2, 5, -20, 21]), 14: set([3, 5, -21]), 15: set([24, 1, -20, 6]), 16: set([6, 2]), 17: set([3, 6, 7, 28, 29]), 18: set([8, 10]), 19: set([10, 12]), 20: set([24, -15, -13]), 21: set([-14, 13, 22]), 22: set([25, 14]), 23: set([-27, 14, 21]), 24: set([8, 15]), 25: set([27, 20, 15]), 26: set([8]), 27: set([-23]), 28: set([7, 27, 28, 29]), 29: set([7, 28, 29]), -1: set([-15, -12, -9]), -29: set([-7, -17]), -28: set([17, -7]), -27: set([-28, -25]), -26: set([-8, 22]), -25: set([-22]), -24: set([-8, -15, -20]), -23: set([]), -22: set([26, -21, 21]), -21: set([-23, -13, -11, 22]), -20: set([-25]), -19: set([11]), -18: set([-8, 12]), -17: set([28]), -16: set([-2, -27]), -15: set([-24, -6, -25]), -14: set([-23, -22, -3]), -13: set([-21, 11, -5]), -12: set([18, -19, -1]), -11: set([19, -4, 13]), -10: set([-2, -12, -19, -18]), -9: set([-8, -1]), -8: set([8, -24, -26, -18, -9]), -7: set([-29, -28]), -6: set([-16, -15, 5, -17]), -5: set([-14, -13, -12, 6]), -4: set([-11, -10, -9]), -3: set([-14, -11, 2, -17]), -2: set([-16, 3, -10, -13])}

# res = graph.Graph()
# for key in [17, 28, 29, 7]:
#     res[key] = g[key]
#     res[(-key)] = g[(-key)]

# {   
#    7: set([-7, 28, 29, 7]), 
#   -7: set([-29, -28]), 
#  -29: set([-7, -17]), 
#  -28: set([17, -7]), 
#   17: set([28, 29, 7]), 
#   29: set([28, 29, 7]),
#   28: set([28, 29, 7]), 
#  -17: set([28])
# }

# ;; Oops .. so here you have a partial graph composition.  When you
# ;; take a couple steps, you end up with a graph that loops.
# ;; Presumably, however, along the way you violate some invariant.  Which
# ;; re-reduces the graph to the one we see here.  And the cycle
# ;; continues forever.

# ;; Perhaps the answer is that we need to avoid composing together elements
# ;; of this set .. at least until we make some sort of progress elsewhere
# ;; in the graph.

## But the bigger question is what reason we have to believe that our 
## algorithm terminates in a SAT or UNSAT state.

## Following is a simple illustration of a similar case:
##
##  a -[  c ] -> !a
## !a -[ !c ] ->  a
##
## This situation is merely similar becuase the loop is only broken 
## in total .. either edge independely would be possible.  In the case
## we were considering, one of the edges itself was ultimately SAT.
##
## Either way, note that there is no contradiction here.  Rather, we 
## know that (a = !c).  Perhaps that would be the only way to resolve the
## conflict .. by replacing a variable with its condition.
##
## At the same time, that sounds awfully hard to back out of.
##

cnf1 = cnf.readCNF("factoring.dimacs")
cg1  = graph.toCondGraph(cnf1)
cg1  = cg1.filterEndpoints()
cgn  = cg1.clone()

ugn  = cgn.unconditionalGraph()
cgn  = cgn.filterCTX(ugn)

cgn.graphInvariant(ugn)

ug1  = cg1.unconditionalGraph()
cg1  = cg1.filterCTX(ug1)

## It should be an invariant that the unconditional graph should
## contain edged for only conditional arcs that are not isTrue()

size = len(cgn.keys())
omit = []
for itr in range(0,20):
    
    # print "omit",omit
    
    # for key in omit:
    #     print    key ,"=>",ugn[   key ]
    #     print (- key),"=>",ugn[(- key)]
    
    ugx  = ugn.clone()
    lps  = ugx.findCycles()
    n = 0
    while (not lps) and (n < size):
        ugx  = ugx.step(omit,ugn)
        lps  = ugx.findCycles()
        n += 1
    
    if (n >= size):
        omit = []
        continue
    
    # for key in omit:
    #     print    key ,"=>",ugx[   key ]
    #     print (- key),"=>",ugx[(- key)]
    
    print "loop depth :",n
    
    minlen = min(len(lps[loop]) for loop in lps)
    res = [loop for loop in lps if (len(lps[loop]) == minlen)]
    loop = res[0]
    lset = lps[loop]
    print loop,"loop contains",lset
    
    print "is",loop,"a loop?",ugx.aLoop(loop)

    for i in range(0,n):
        cgn.step(lset,cg1,ugn)
        cgn.graphInvariant(ugn)
    
    ## I think we want a function that will filter
    ## (and filter endpoints) just the loop ..
    ## Actually, I think we should do this as part
    ## of composition.  Again, we are only making
    ## the graph stronger.
    
    ## But you understand that you are making the graph unsound in the
    ## process.  I think that is OK.  We still expect to heal it
    ## eventually.  In other words: we want to keep the unconditional
    ## graph in sync with the conditional graph.
    
    print "is",loop,"a loop?",ugn.aLoop(loop)
    assert not ugn.aLoop(loop),"Hey, we've got a live one here!"
    
    omit = omit + list(lset) + [ (- x) for x in lset ]
    
    cgn  = cgn.filterCTX(ugn)
    cgn.graphInvariant(ugn)
    
    print "Looping :",itr

## Are loops still valid?

##cg4  = cg3.filterCTX(ug1)
##cg5  = cg4.filterCTX(ug1)

# ug2  = cg2.unconditionalGraph()
# ## Note: we always filter the initial graph
# cg3  = cg1.filterCTX(ug2)
# ug3  = cg3.unconditionalGraph()
# cg4  = cg1.filterCTX(ug3)

##
## We need to keep SAT edges around .. they may eventuall become UNSAT.
##
## Note that is is possible to reduce the SAT of a given clause down to
## a relationship between 3 variables.  This would allow us to track
## dependencies and quickly determine when the removal of an edge in the
## graph would result in the release of a SAT edge.
##

## One issue we face is that, when we drop an edge, we weaken the graph.
## Thus, it is not really possible to process all of the possible drops
## at the same time.  Rather, we are forced to consider 

## No .. when we drop an edge we simply weaken the unconditional graph.
## This will allow us to process the entire graph, but with an increasinly
## weak unconditional graph.

## As we weaken the graph, edges in the SAT set may be activated.  Thus,
## weakening in one dimension may actually strengthen in another.

## The key invarient that we want to maintain is that the SAT set
## contain only satisfied claues.

## I suppose that SAT clauses could be stored in a data structure keyed
## by the affected variables (?) .. 

## [ ((a . b) (c . d) (e .f)) clause ]

## (shared . psrc . nsrc)

## (Graph . SATset)

## Adding a constraint to a graph makes it stronger.
## That may satisfy new graph edges, moving them to SATsat
## .. but that will weaken the graph.

## src dst c1 c2 c3

## (src dst UNSAT:(c1 c2) SAT:(c3 c4))

## There is no rush to move elements from SAT to UNSAT ..
## we are more concerned about moving UNSAT to SAT, esp.
## when UNSAT is empty.

## When you weaken the graph, you may move clauses from
## SAT to UNSAT.  For partial CNF this isn't a big deal,
## but you do want to make sure they are accurate prior
## to, once again, strengthening the graph.

## It is a bigger deal for UNSAT edges, because if we
## can move *any* clause from SAT to UNSAT, we restore
## the edge.

## After we weaken the graph we need to re-evaluate
## all of the UNSAT clauses, possibly re-enstating
## UNSAT edges.

#
# When we filter the graph (weaken it), we ..
#
# 1. for each edge, filter UNSAT cnf
# 2. If UNSAT is empty,
#      double check SAT clauses
# 3. If UNSAT is (really) empty,
#      remove edge (weaker)
#      re-activate any dependent (now UN) SAT clauses (stronger)
#        of course, double check UNSAT
# 4. When done, re-evaluate graph SAT sets
#    - SAT sets in graph may be wrong during weakening
#
# When done, some graph conditions may be SAT
# - but all SAT conditions are SAT
#
# Of course, you could always run the algorithm again .. 
#



## When you do composition, 

## You really need a way to mark clauses as SAT within the CNF.
## Of course that messes everything up.  How about we have the
## 

## [ (s1 s2) [ (var . clause) .. ]
##   (sa sb) ..

## If you disconnect all of the edges, it allows a wider
## variety of solutions .. but edges are clauses .. so
## unless the graph really 

## I suppose you 

## Yeah, that makes a big difference.  Ugh ..
## it is not obvious 

## I'm not sure about this .. I'm concerned about
## unsound deductions .. by weakening 

## I supect that we may need to perform this
## process multiple times.
