"""Rational weighted-conic normal form and exact incidence checks."""
from fractions import Fraction
from itertools import combinations
from flint import nmod_mat, fmpq_mat

if not __debug__:
    raise RuntimeError('This exact verifier requires assertions; do not use -O.')


def cross(a,b):
    return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]


def normal_form(lines,weights):
    lines=[[Fraction(c) for c in row] for row in lines]
    w=[Fraction(c) for c in weights]
    assert len(lines)==len(w)==5 and all(len(row)==3 for row in lines)
    assert all(w) and sum(w)==1
    A=[[Fraction(int(i==j)) if i<3 and j<3 else Fraction(0)
        for j in range(7)] for i in range(7)]
    for i in range(4):
        for j in range(4):
            A[i+3][j+3]=Fraction(int(i==j))/w[i]+1/w[4]
    L=[]
    for k in range(3):
        e=[Fraction(int(i==k)) for i in range(3)]
        rows=[e+[Fraction(0)]*4]
        for r,v in enumerate(lines):
            rows.append(cross(v,e)+[v[k]*(int(r==j)-w[j]) for j in range(4)])
        L.append(rows)
    return L,A


def verify_incidence(L,A):
    J=[1,-1,-1,-1,-1,-1]
    for i in range(3):
        for j in range(3):
            for a in range(6):
                for b in range(6):
                    x=sum(L[i][a][u]*A[u][v]*L[j][b][v]
                          for u in range(7) for v in range(7))*J[b]
                    y=sum(L[j][a][u]*A[u][v]*L[i][b][v]
                          for u in range(7) for v in range(7))*J[a]
                    assert x==y,(i,j,a,b,x,y)
    return True


def reduce_mod(L,p):
    def mod(q):
        q=Fraction(q)
        return q.numerator*pow(q.denominator,-1,p)%p
    return [[[mod(c) for c in row] for row in m] for m in L]


def open_ranks(L,p=101):
    if p is not None:
        L=reduce_mod(L,p)
    J=[1,-1,-1,-1,-1,-1]
    R=[[[J[u]*L[i][u][e] for e in range(7)] for u in range(6)] for i in range(3)]
    wedge=list(combinations(range(6),2))
    F=[[int(u==b)*L[i][a][e]-int(u==a)*L[i][b][e]
        for u in range(6) for e in range(7)] for i in range(3) for a,b in wedge]
    N=[[L[i][u][e]*int(k==j)
        for i in range(3) for u in range(6) for k in range(3)]
       for e in range(7) for j in range(3)]
    N += [[R[k][u][e]*int(h==i)
           for h in range(3) for u in range(6) for k in range(3)]
          for i in range(3) for e in range(7)]
    recovery=[[L[i][a][t]*R[j][b][v]-R[j][a][v]*L[i][b][t]
               for v in range(7) for t in range(7)]
              for i in range(3) for j in range(3) for a,b in wedge]
    rank=lambda m: nmod_mat(m,p).rank() if p is not None else fmpq_mat([[str(c) for c in row] for row in m]).rank()
    ranks={name:rank(m) for name,m in
           [('F',F),('N',N),('recovery',recovery)]}
    assert ranks=={'F':39,'N':36,'recovery':48},ranks
    return ranks
