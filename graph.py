import random
from cnf import *

class Var():
    
    nextID = 1
    
    @staticmethod
    def alloc():
        res = Var.nextID
        Var.nextID += 1
        return res
    
    @staticmethod
    def avoid(lit):
        Var.nextID = max(abs(lit)+1,Var.nextID)
    
    @staticmethod
    def avoidSet(clause):
        for e in clause:
            Var.avoid(e)

class condSet(dict):
    
    def __missing__(self, key):
        return CNF.true()
    
    def __init__(self, *args, **kwargs):
        self.init_update(*args, **kwargs)
    
    def init_update(self, *args, **kwargs):
        for k, v in dict(*args, **kwargs).iteritems():
            self[k] = v
    
    def __setitem__(self, key, val):
        if not val.isTrue():
            dict.__setitem__(self, key, val)
        else:
            self.pop(key,None)
    
    def copy(self):
        return copy.copy(self)
    
    def update(self,dst,cond):
        """
        Procedure updates Dset with dst:cnf
        """
        self[dst] = cond.andCNF(self[dst])
        return self
    
    def orCond(self,cond):
        """
        Procedure or's cond into all conditions
        """
        res = self.copy()
        for key in self.keys():
            res[key] = cond.orCNF(res[key])
        return res

    def merge(self,cset):
        """
        Procedure (parallel) merges cset into this cset.
        """
        for (key,cond) in cset.iteritems():
            self.update(key,cond)
        return self
    
    def filterEndpoints(self,src):
        res = condSet()
        for key in self.keys():
            cond = self[key]
            cond = cond.filterEndpoint(key)
            cond = cond.filterEndpoint(- src)
            res[key] = cond
    
    def filterCTX(self,ctx,cond):
        res = condSet()
        for dst in self.keys():
            dcond = ctx[(- dst)]
            zed   = self[dst]
            zed   = zed.filterCTX(ctx,cond)
            zed   = zed.filterCTX(ctx,dcond)
            res[dst] = zed
        return res

class condGraph(dict):
    
    def __missing__(self, key):
        return condSet()
    
    def copy(self):
        return copy.copy(self)
    
    def addArc(self,src,cond,dst):
        mp = self[src]
        mp[dst] = cond.andCNF(mp[dst])
        self[src] = mp
        return
    
    def add2Clause(self,x,y,cond):
        self.addArc((- x),cond,y)
        self.addArc((- y),cond,x)
        return
    
    def filterEndpoints(self):
        res = condGraph()
        for src in self.keys():
            res[src] = self[src].filterEndpoints(src)
        return res
    
    def filterCTX(self,ctx):
        res = condGraph()
        for src in self.keys():
            cond = ctx[src]
            res[src] = self[src].filterCTX(ctx,cond)
        return res
    
    def step(self,g0):
        res = condGraph()
        for (src,dset) in self.iteritems():
            for (dst,cond) in dset.iteritems():
                res[src] = g0[src].merge(self[src].merge(g0[dst].orCOND(cond)))
        return res
    
    def unconditionalGraph(self):
        res = Graph()
        for src in self.keys():
            res[src] = Clause(self[src].keys())
        return res

class Graph(dict):
    
    def __missing__(self, key):
        return frozenset()
    
    def addSet(self,src,zset):
        self[src] = self[src].union(zset)
        return this
    
    def addElement(self,src,z):
        self[src] = self[src].union([z])
        return this
    
    def getSet(self,sset):
        res = frozenset()
        for key in sset:
            res = res.union(self[key])
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
