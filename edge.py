import cnf

## Filtering a CNF produces a new CNF and a SAT set.
## 

def extractImplication(src,dst,satlist):
    miss = []
    hits = []
    for entry in satlist:
        (z,x,y,cond) = entry
        if ((z == dst) and ((src == x) or (src == y))):
            hits += entry
        else:
            miss += entry
    return (hits,miss)

class edge():
    
    def __init__(self,src,dst):
        self.src   = src
        self.dst   = dst
        self.deps  = edgeSet()
        self.unsat = cnf.CNF.true()
        self.sat   = []
    
    def equiv(self,target):
        srceq = (self.src == target.src)
        dsteq = (self.dst == target.dst)
        return (srceq and dsteq)
    
    def isAlwaysTrue(self):
        return self.unsat.isTrue() and (not self.sat)

    def isTrue(self):
        return self.unsat.isTrue()
    
    def unregister(self,satset,gr):
        for (z,x,y,cond) in satset:
            gr[x][z].deps.remove(this)
            gr[y][(- z)].deps.remove(this)

    def register(self,satset,gr):
        for (z,x,y,cond) in satset:
            gr[x][z].deps.add(self)
            gr[y][(- z)].deps.add(self)

    def reEvalSATlist(oldsatlist,src,dst,ctx):
        cnfres  = cnf.CNF.true()
        newsatlist = []
        for (z0,x0,y0,cond) in oldsatlist:
            sat = cond.SATcore(src,dst,ctx)
            if sat:
                newsatlist.append(sat)
            else:
                cnfres.andClause(cond)
        return (cnfres,newsatlist)
    
    def filterEndpoints(self):
        assert(False)

    def filterCTX(self,gr,ctx):
        """
        filterCTX() applies the (presumably) stronger graph ctx to the
        current (UNSAT) edge.  If, as a result of filtering, the edge
        is SAT, we update (weaken) ctx, register the edge with its
        dependencies, and then re-evaluate all of the edges that depend
        upon this edge.
        """
        if self.cnf.isTrue():
            return
        (cnf,newsat) = self.cnf.filterCTX(ctx)
        self.sat.append(newsat)
        self.cnf = cnf
        if self.cnf.isTrue():
            ctx[src].discard(dst)
            self.register(self.sat,gr)
            ## Make a copy of the deps .. it will be changing
            deps = [ edge for edge in self.deps ]
            for edge in deps:
                edge.reEvalEdge(src,dst,gr,ctx)

    def reEvalEdge(self,src,dst,gr,ctx):
        """
        reEvalEdge() is applied to a (presumably) SAT edge where one
        of the edges upon which it depends (ie: src,dst) no longer
        exists in ctx.  Each SAT condition that previously depended
        upon the src,dst edge must be re-evaluated in the current
        context.  The edge may now be UNSAT or it may still be SAT,
        but with a new SAT core.  Either way we unregister the old
        dependencies.  If the edge remains SAT, we register the new
        SAT core.  If the re-evaluated edge is UNSAT we unregister all
        of the dependencies and strengthen the graph ctx.
        """
        assert(self.cnf.isTrue())
        (oldsatlist,sat) = extractImplication(src,dst,self.sat)
        (cnf,newsatlist) = reEvalSATlist(oldsatlist,self.src,self.dst,ctx)
        self.cnf = self.cnf.andCNF(cnf)
        self.unregister(oldsatlist,gr)
        if self.cnf.isTrue():
            self.register(newsatlist,gr)
        else:
            self.unregister(sat,gr)
            ctx[self.src].add(self.dst)
        sat.append(newsatlist)
        self.sat = sat

class edgeSet(list):
    
    def indexOf(self,edge):
        index = 0
        for e in self:
            if e.equiv(edge):
                return index
            index += 1
        return None
    
    def add(self,edge):
        index = self.indexOf(edge)
        if index:
            self[index] = edge
        else:
            self.add([edge])
    
    def remove(self,edge):
        index = self.indexOf(edge)
        if index:
            del self[index]
