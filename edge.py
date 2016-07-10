import cnf

## Yeah, we really should make satlist its own class ..

def extractImplication(src,dst,satlist):
    miss = []
    hits = []
    for entry in satlist:
        (z,x,y,cond) = entry
        if ((z == dst) and ((src == x) or (src == y))):
            hits.append(entry)
        else:
            miss.append(entry)
    return (hits,miss)

def SATtoCNF(satlist):
    cnfres  = cnf.CNF.true()
    for (z0,x0,y0,cond) in satlist:
        cnfres = cnfres.andClause(cond)
    return cnfres

class edge():
    
    def __init__(self,src,dst,cnf0 = cnf.CNF.true()):
        self.src   = src
        self.dst   = dst
        self.deps  = edgeSet()
        self.cnf   = cnf0
        self.sat   = []
    
    def equiv(self,target):
        srceq = (self.src == target.src)
        dsteq = (self.dst == target.dst)
        return (srceq and dsteq)
    
    def __str__(self):
        return str(self.src) + " =" + str(self.cnf) + "=> " + str(self.dst)
    
    __repr__ = __str__
    
    def isAlwaysTrue(self):
        return self.cnf.isTrue() and (not self.sat)

    def isTrue(self):
        return self.cnf.isTrue()
    
    def unregister(self,satset,gr):
        print "unregister satset : " + str(satset)
        for (z,x,y,cond) in satset:
            gr[x][z].deps.remove(self)
            gr[y][(- z)].deps.remove(self)

    def register(self,satset,gr):
        print "register satset : " + str(satset)
        for (z,x,y,cond) in satset:
            gr[x][z].deps.add(self)
            gr[y][(- z)].deps.add(self)

    def filterEndpoints(self):
        self.cnf = self.cnf.filterEndpoints((- self.src))
        self.cnf = self.cnf.filterEndpoints(self.dst)
    
    def filterCTX(self,gr,ctx):
        """
        filterCTX() applies the (presumably) stronger graph ctx to the
        current (UNSAT) edge.  If, as a result of filtering, the edge
        is SAT, we update (weaken) ctx, register the edge with its
        dependencies, and then re-evaluate all of the edges that depend
        upon this edge.
        """
        print "Filtering Edge : " + str(self)
        if self.cnf.isTrue():
            return
        (cnf,newsat) = self.cnf.filterCTX(self.src,self.dst,ctx)
        self.sat.extend(newsat)
        self.cnf = cnf
        if self.cnf.isTrue():
            print "Dropping Satisfied Edge : " + str(self)
            ctx[self.src].discard(self.dst)
            ## Register this node as dependent on the SAT set ..
            self.register(self.sat,gr)
            ## Make a copy of the deps .. it will be changing
            deps = [ edge for edge in self.deps ]
            for edge in deps:
                edge.reEvalEdge(self.src,self.dst,gr,ctx)
        gr.checkDEPS()

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
        print "Re-Evaluating Edge : " + str(self)
        ##
        ## A satisfied condition ought not depend upon the edge
        ## that it guards.
        ##
        assert(self.cnf.isTrue())
        (updatesat,unchangesat) = extractImplication(src,dst,self.sat)
        self.unregister(updatesat,gr)
        cnf = SATtoCNF(updatesat)
        (cnf,newsatlist) = cnf.filterCTX(self.src,self.dst,ctx)
        self.cnf = self.cnf.andCNF(cnf)
        if self.cnf.isTrue():
            self.register(newsatlist,gr)
        else:
            print "Adding UNSAT Edge : " + str(self)
            self.unregister(unchangesat,gr)
            ctx[self.src].add(self.dst)
        unchangesat.extend(newsatlist)
        self.sat = unchangesat

class edgeSet(list):
    
    def __init__(self):
        self.value = []
    
    def __iter__(self):
        return iter(self.value)
    
    def indexOf(self,edge):
        index = 0
        for e in self.value:
            if e.equiv(edge):
                return index
            index += 1
        return None
    
    def add(self,edge):
        index = self.indexOf(edge)
        if index is not None:
            self.value[index] = edge
        else:
            self.value.append(edge)
    
    def remove(self,edge):
        index = self.indexOf(edge)
        if index is not None:
            self.value.pop(index)
