## Utility functions for manipulatinng CNFs, Clauses and other
## relevant data structures.

import sys
from collections import Counter

class rewriteArray(dict):
    def __missing__(self, key):
        return key

class forwardArray(dict):
    def __missing__(self, key):
        return frozenset()

class Clause(frozenset):
    
    @staticmethod
    def false():
        return Clause()
    
    def __str__(self):
        return str(list(self))
    
    def removeConflicts(self):
        return Clause([ lit for lit in self if (- lit) not in self])
    
    def orClause(self,clause):
        """
        Function computes the raw 'or' with the given clause
        """
        return self.union(clause)
    
    def negate(self):
        """
        Function negates all of the elements of the clause
        """
        return Clause([ (- x) for x in self ])
    
    def isTrue(self):
        """
        Function checks a clause for contradiction (x + !x) 
        """
        for lit in self:
            if (- lit) in self:
                return True
        return False
    
    def isTrueCTX(self,ctx,clause):
        """
        Function checks if a clause is true in the current
        graph context
        """
        for key in self:
            clause = clause.union([(- key)])
            clause = clause.union(ctx[(- key)])
        res = clause.isTrue()
        if res:
            print "Dropping Clause : " + str(clause)
        return res

    def isFalse(self):
        """
        Function checks if a clause if False
        """
        return not(self)
    
    def remove(self,key):
        if key in self:
            return Clause([lit for lit in self if not key == lit])
        return self

    def conflictedVariables(self,target):
        """
        Function computes the set of conflicted variables in a clause
        """
        res = set([])
        for lit in self:
            if (- lit) in target:
                res.add(abs(lit))
        return res
    
    def forward(self,ctx):
        res = self
        for lit in self:
            res = res.union(ctx[lit])
        return res
    
    def findConflict(self,fwd,ctx):
        for lit in self:
            if ((fwd == lit) or (fwd in ctx[lit])):
                return lit
        print ctx
        assert(False)
        return None
    
    def SATcore(self,src,dst,ctx):
        """
        This function computes the SAT core of an implication of the form
        (src -> dst unless self) which corresponds to a clause of the
        form (!src + self + dst).  This clause is SAT if the term (src
        & !self & !dst) leads to a contradiction.  If that term leads
        to a contradiction, the clause can be reduced to one of the
        form (!x + !y) where x => z and y => !z.  If the clause is
        SAT, we return (z,x,y).  If the clause is not SAT, we return
        None.  Note: we do not consider !src or dst or (!src + dst) to
        be valid SAT cores even when they are SAT.
        """
        negclause = self.negate()
        deductions = negclause.forward(ctx)
        clist = deductions.conflictedVariables(deductions)
        if clist:
            cvar = clist.pop()
            x = negclause.findConflict(cvar,ctx)
            y = negclause.findConflict((- cvar),ctx)
            return (cvar,x,y,self)
        ##
        ## We need to remove conflicts because if the
        ## src implication has both z and (- z) and
        ## only one is part of the conflict then if
        ## we choose the wrong one, we cannot find the
        ## other with findConflict.
        ## 
        srcctx = ctx[src].union([src])
        srcctx.discard(dst)
        srcdeductions = Clause(srcctx).removeConflicts()
        clist = deductions.conflictedVariables(srcdeductions)
        if clist:
            cvar = clist.pop()
            # print "neg  : ",negclause
            # print "ded  : ",deductions
            # print "src  : [",src,"]",srcdeductions
            # print "cvar : ",cvar
            if cvar in srcdeductions:
                x = src
                y = negclause.findConflict((- cvar),ctx)
            else:
                x = negclause.findConflict(cvar,ctx)
                y = src
            return (cvar,x,y,self)
        dstctx = ctx[(- dst)].union([(- dst)])
        dstctx.discard((- src))
        dstdeductions = Clause(dstctx).removeConflicts()
        clist = deductions.conflictedVariables(dstdeductions)
        if clist:
            cvar = clist.pop()
            # print "neg  : ",negclause
            # print "ded  : ",deductions
            # print "dst  : [",dst,"]",dstdeductions
            # print "cvar : ",cvar
            if cvar in dstdeductions:
                x = (- dst)
                y = negclause.findConflict((- cvar),ctx)
            else:
                x = negclause.findConflict(cvar,ctx)
                y = (- dst)
            return (cvar,x,y,self)
        return None

class CNF(list):
    
    @staticmethod
    def false():
        return CNF([Clause.false()])
    
    @staticmethod
    def true():
        return CNF()
    
    def __str__(self):
        res = [ str(clause) for clause in self ]
        return str(res)
    
    def subsumesClause(self,clause):
        """
        Function checks to see if the clause is subsumed (<=) by an entry in the CNF
        """
        for entry in self:
            if entry <= clause:
                return True
        return False
    
    def removeSubsumedClauses(self):
        """
        Function removes subsumed clauses from CNF
        """
        res = CNF()
        for clause in self:
            if not res.subsumesClause(clause):
                res.append(clause)
        return res
    
    def isTrue(self):
        """
        Function checks if CNF is true
        """
        return not(self)
    
    def filterCTX(self,src,dst,ctx):
        cnfres  = CNF.true()
        satlist = []
        for clause in self:
            sat = clause.SATcore(src,dst,ctx)
            if sat:
                satlist.append(sat)
            else:
                cnfres = cnfres.andClause(clause)
        return (cnfres,satlist)
    
    def isFalse(self):
        """
        Function checks if CNF is false
        """
        if len(self) == 1:
            [clause] = self
            return clause.isFalse()
        return False
    
    def andClause(self,clause):
        """
        Function and's clause with cnf
        """
        if self.subsumesClause(clause):
            return self
        cnf = CNF([ c for c in self if not clause <= c ])
        cnf.append(clause)
        return cnf
    
    def andCNF(self,new):
        """
        Function ands the current CNF with a new CNF
        """
        cnf = self
        for clause in new:
            cnf = cnf.andClause(clause)
        return cnf
    
    def orLit(self,lit):
        res = CNF();
        for clause in self:
            if (- lit) in clause:
                continue
            res.append(clause.union([lit]))
        return res
    
    def orCNF(self,y):
        """
        Function computes the or of CNF's x and y
        """
        x = self
        if x.isTrue(): return x
        if y.isTrue(): return y
        xy = [ a.orClause(b) for a in x for b in y ]
        z  = CNF([ clause for clause in xy if not clause.isTrue() ])
        return z.removeSubsumedClauses()
    
    def notCNF(self):
        """
        Function negates the CNF
        """
        res = CNF([Clause.false()])
        for clause in self:
            res = res.orCNF(CNF([Clause([(- lit)]) for lit in clause]))
        return res
    
    def filterEndpoint(self,key):
        cnf = CNF([ clause.remove(key) for clause in self if not (- key) in clause])
        return cnf

def maxSize(cnf):
    res = 1
    for clause in cnf:
        res *= len(clause)
    return res

def chooseMin(cnf1,cnf2):
    if (maxSize(cnf1) < maxSize(cnf2)):
        return cnf1
    return cnf2

#
# Read CNF file
#

def stringToClause(ln):
    return Clause([int(word) for word in ln.split() if int(word) != 0])

# sys.sargv[1]
def readCNF(file):
  with open(file) as f:
    cnf = CNF([stringToClause(line) for line in f if (line[0] != "%" and line[0] != "c" and line[0] != "p")])
  return cnf
