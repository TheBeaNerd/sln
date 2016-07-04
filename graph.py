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
        if not val.isAlwaysTrue():
            dict.__setitem__(self, key, val)
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
        edge.unsat = cond.andCNF(edge.unsat)
        emap[dst] = edge
        self[src] = emap
        return self
    
    def add2Clause(self,x,y,cond):
        self.addArc((- x),cond,y)
        self.addArc((- y),cond,x)
        return self
    
    def filterEndpoints(self):
        for (src,emap) in self.iteritems():
            for (dst,edge) in emap.iteritems():
                emap[dst].filterEndpoints()
        return self

    def filterCTX(self,ctx):
        for (src,emap) in self.iteritems():
            for (dst,edge) in emap.iteritems():
                emap[dst].filterCTX(self,ctx)
        return self
    
    def step(self,g0):
        res = condGraph()
        for (src,emap) in self.iteritems():
            for (dst,edge) in emap.iteritems():
                res[src] = g0[src].merge(self[src].merge(g0[dst].orCOND(cond)))
        return res
    
    def unconditionalGraph(self):
        res = Graph()
        for src in self.keys():
            res.addSet(src,self[src].keys())
        return res

class Graph(dict):
    
    def __missing__(self, key):
        return set()
    
    def addSet(self,src,zset):
        xset = self[src]
        xset.update(zset)
        self[src] = xset
        return this
    
    def addElement(self,src,z):
        xset = self[src]
        xset.add(z)
        self[src] = xset
        return this
    
    def getSet(self,sset):
        res = set()
        for key in sset:
            res.update(self[key])
        return res

    def step(self,g):
        res = Graph()
        for key in g.keys():
            dst = self[key]
            res[key] = dst.union(getSet(dst))
        return res

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
