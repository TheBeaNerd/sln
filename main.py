import graph
import cnf

cnf1 = cnf.readCNF("factoring.dimacs")
cg1  = graph.toCondGraph(cnf1)
cg2  = cg1.filterEndpoints()
ug1  = cg2.unconditionalGraph()
cg3  = cg2.filterCTX(ug1)
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
