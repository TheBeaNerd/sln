import random
from cnf import *
from edge import *
from copy import copy

class edgeMap(dict):
    
    def __init__(self,src):
        self.src = src
    
    def __missing__(self,dst):
        return edge(self.src,dst)
    
    def __setitem__(self, key, edge):
        if not edge.isAlwaysTrue():
            dict.__setitem__(self, key, edge)
        else:
            self.pop(key,None)

    def filterCTX(self,src,gr,ctx):
        for dst in self.keys():
            self[dst].filterCTX(src,dst,gr,ctx)
        return self

class condGraph(dict):
    
    def __missing__(self, src):
        return edgeMap(src)
    
    def addArc(self,src,cond,dst):
        emap = self[src]
        edge = emap[dst]
        edge.cnf = cond.andCNF(edge.cnf)
        emap[dst] = edge
        self[src] = emap
        return self
    
    def checkDEPS(self):
        for (src,emap) in self.iteritems():
            for (dst,edge) in emap.iteritems():
                for sedge in edge.deps:
                    assert sedge.cnf.isTrue(), "edge %s thinks edge %s is SAT" % (str(edge),str(sedge))

    def add2Clause(self,x,y,cond):
        self.addArc((- x),cond,y)
        self.addArc((- y),cond,x)
        return self
    
    def filterEndpoints(self):
        for (src,emap) in self.iteritems():
            for (dst,edge) in emap.iteritems():
                edge.filterEndpoints()
        return self
    
    def filterCTX(self,ctx):
        for (src,emap) in self.iteritems():
            for (dst,edge) in emap.iteritems():
                edge.filterCTX(self,ctx)
                self[(- dst)][(- src)].filterCTX(self,ctx)
        return self
    
    ## Our fixpoint graph must be a clone of our step graph
    ## (They cannot share edges).  We will need to re-filter
    ## both our step graph and our fixpoint graph after each step.
    def clone(self):
        res = condGraph()
        for (src,emap) in self.iteritems():
            rmap = res[src]
            for (dst,dedge) in emap.iteritems():
                rmap[dst] = edge(src,dst,dedge.cnf.andCNF(SATtoCNF(dedge.sat)))
            res[src] = rmap
        return res

    ## The stepping process updates the stepped graph
    ## Presumably, you are making the graph stronger
    ## Things that were SAT before should be SAT now
    ## Things that were UNSAT before might be SAT now
    def step(self,loop,g1,ctx):
        for (src,sdmap) in self.iteritems():
            if src in loop:
                for (dst,sdedge) in list(sdmap.iteritems()):
                    if (dst in loop) and (not sdedge.isTrue()):
                        dxmap = g1[dst]
                        for (xdst,dxedge) in dxmap.iteritems():
                            if (xdst in loop) and (not dxedge.isTrue()):
                                redge = sdmap[xdst]
                                cnf = sdedge.cnf.orCNF(dxedge.cnf)
                                cnf = cnf.filterEndpoints((- src))
                                cnf = cnf.filterEndpoints(xdst)
                                (cnf,sat) = cnf.filterCTX(src,xdst,ctx)
                                cnf = redge.cnf.andCNF(cnf)
                                if not cnf.isTrue():
                                    if redge.cnf.isTrue():
                                        redge.unregister(redge.sat,self)
                                    redge.cnf = cnf
                                    redge.sat.extend(sat)
                                    sdmap[xdst] = redge
                                    ctx[src].add(xdst)
                                    ##print "Added edge from ",src,"to",xdst
                                    self.checkDEPS()
    
    def unconditionalGraph(self):
        res = Graph()
        for (src,emap) in self.iteritems():
            for (dst,edge) in emap.iteritems():
                if not edge.isTrue():
                    res.addElement(src,dst)
        return res
    
    def graphInvariant(self,ug):
        assert set(self.keys()) == set(ug.keys()), "src key sets differ"
        for (src,emap) in self.iteritems():
            dset = ug[src]
            cset = set(emap.keys())
            assert dset.issubset(cset), "unconditional implications %s from %d are not in conditional graph" % (str(list(dset - cset)),src)
            for (dst,edge) in emap.iteritems():
                if dst in dset:
                    assert not edge.cnf.isTrue(),"unconditional implication %d despite SAT guard from %d" % (dst,src)
                else:
                    assert edge.cnf.isTrue(),"missing unconditional implication %d despite UNSAT guard from %d" % (dst,src)


def abset(slist):
    return set([abs(lit) for lit in slist])

def pairs(slist):
    return set([ abs(key) for key in slist if (- key) in slist ])

class Graph(dict):
    
    def __missing__(self, key):
        return set()
    
    def addSet(self,src,zset):
        xset = self[src]
        xset.update(zset)
        self[src] = xset
        return self
    
    def addElement(self,src,z):
        xset = self[src]
        xset.add(z)
        self[src] = xset
        return self
    
    def getSet(self,sset):
        res = set()
        for key in sset:
            res.update(self[key])
        return res

    def clone(self):
        res = Graph()
        for key in self.keys():
            res[key] = set(self[key])
        return res

    def step(self,omit,g):
        res = Graph()
        for key in g.keys():
            dst = self[key]
            if key in omit:
                dst = [ x for x in dst if x not in omit ]
            res[key] = self[key].union(self.getSet(dst))
        return res

    def inLoop(self,key,z):
        pkey = self[key]
        nkey = self[(- key)]
        return (((- z) in pkey) and (z in pkey) and
                ((- z) in nkey) and (z in nkey))
    
    def aLoop(self,key):
        pkey = self[key]
        nkey = self[(- key)]
        return ((key in nkey) and ((- key) in pkey))

    def findCycles(self):
        loopingkeys = []
        loops = {}
        for key in abset(self.keys()):
            if ((key not in loopingkeys) and self.aLoop(key)):
                ## If x -> -x and -x -> x then any node from
                ## x that reaches -x and any node from -x that
                ## reaches x are part of the loop.
                pbody = self[key]
                ploop = [abs(z) for z in pbody if (- key) in self[z]]
                nbody = self[(- key)]
                nloop = [abs(z) for z in nbody if key in self[z]]
                loop = set(ploop + nloop)
                loop.add(key)
                loops[key] = loop
                loopingkeys += loop
        return loops

## So, technically, I suppose it is true that when we choose two
## literals to add to the clause, we are effectively assuming that the
## other literals are false.  We could try to be more consistent about
## this when we construct the initial graph.

def toCondGraph(cnf):
    res = condGraph()
    for clause in cnf:
        if (len(clause) > 1):
            cond = list(clause)
            src = random.choice(cond)
            cond.remove(src)
            dst = random.choice(cond)
            cond.remove(dst)
            res.add2Clause(src,dst,CNF([Clause(cond)]))
        elif (len(clause) > 0):
            lit = list(clause)[0]
            res.addArc((- lit),CNF.false(),lit);
        else:
            pass
    return res

##
## Condition filtering will weaken 2the deductive power
## of a graph.  But that would seem to imply that the
## graph will become weaker .. which would imply that
## 
##  a + !a + b
##
## At the same time, you want the graph to be weak.
## 
