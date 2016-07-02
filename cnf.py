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

    def conflictedVariables(self):
        """
        Function computes the set of conflicted variables in a clause
        """
        res = set([])
        for lit in self:
            if (- lit) in self:
                res.add(abs(lit))
        return res
    
    ##
    ## Counting Variables/Literals
    ##
    
    def addClauseVariables(self,cnt):
        cnt.update([abs(lit) for lit in clause])
        return cnt
    
    def remClauseVariables(self,cnt):
        cnt = cnt - Counter([abs(lit) for lit in self])
        return cnt

    def addClauseLiterals(self,cnt):
        cnt.update([lit for lit in self])
        return cnt

    def remClauseLiterals(self,cnt):
        cnt = cnt - Counter([lit for lit in self])
        return cnt

class CNF(list):
    
    @staticmethod
    def false():
        return CNF([Clause.false()])

    @staticmethod
    def true():
        return CNF()

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
    
    def filterCTX(self,ctx,clause):
        return CNF([cl for cl in self if not cl.isTrueCTX(ctx,clause)])
    
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
    
    ##
    ## Counting Variables/Literals
    ##
    
    def addCNFLiterals(self,cnt):
        for clause in self:
            cnt = addClauseLiterals(clause,cnt)
        return cnt
    
    def remCNFLiterals(self,cnt):
        for clause in self:
            cnt = remClauseLiterals(clause,cnt)
        return cnt
    
    def addCNFVariables(self,cnt):
        for clause in self:
            cnt = addClauseVariables(clause,cnt)
        return cnt

    def remCNFVariables(self,cnt):
        for clause in self:
            cnt = remClauseVariables(clause,cnt)
        return cnt

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
