#!/usr/bin/env python3
"""Exact normalized bar verification for the two nonzero m=3 VK corners.

The multiplication is built directly from the finite CGG formula, independently
of the deformation-hull proof. Paths are multiplied in their written order;
changing the End convention takes the opposite algebra and preserves HH.
Normal execution writes no files. The certificate is compared by verify_v35.py.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, product
import json
from flint import fmpq, fmpq_mat


ZERO=(0,0,0,0)
WEIGHTS=(1,1,1,3)
OBJECTS=(0,1,3,4)

def require(ok,msg):
    if not ok: raise RuntimeError(msg)

def plus(a,b):return tuple(x+y for x,y in zip(a,b))

def add(poly,mon,c):
    if not c:return
    poly[mon]=poly.get(mon,Q(0))+c
    if not poly[mon]:del poly[mon]

def times(a,b):
    out={}
    for u,c in a.items():
        for v,d in b.items():add(out,plus(u,v),c*d)
    return out

@lru_cache(None)
def basis(degree):
    ans=[]
    for w in range(degree//3+1):
        rem=degree-3*w
        for x in range(rem+1):
            for y in range(rem-x+1):ans.append((x,y,rem-x-y,w))
    return tuple(ans)

@lru_cache(None)
def cochains(n):
    ans=[]
    for chain in combinations(OBJECTS,n+1):
        pieces=[basis(chain[i+1]-chain[i]) for i in range(n)]
        for inputs in product(*pieces):
            for out in basis(chain[-1]-chain[0]):ans.append((chain,inputs,out))
    return tuple(ans)

def make_product(j,r,alpha,s):
    require(2*j+r==3,'m=3 only')
    d=3+r+1
    if j==0:P={(0,0,r,0):Q(1)}
    else:P={(1,0,r+1,0):Q(1),(0,2,r,0):Q(-1)}
    fields=[{}, {(1,0,0,0):Q(1)}, {(0,1,0,0):Q(2)}, {u:-c for u,c in P.items()}]
    def N(poly):
        out={}
        for u,c in poly.items():
            for i,v in enumerate(u):
                if not v or not fields[i]:continue
                z=list(u);z[i]-=1;z=tuple(z)
                for f,e in fields[i].items():add(out,plus(z,f),c*v*e)
        return out
    @lru_cache(None)
    def mono(a,b):
        weight=alpha*sum(w*x for w,x in zip(WEIGHTS,b))+b[1]+2*b[2]+d*b[3]
        derivative={a:Q(1)};out={};choose=Q(1);power=Q(1);n=0
        while derivative:
            for u,c in derivative.items():add(out,plus(u,b),power*choose*c)
            n+=1;choose*= (weight-(n-1))/n;power*=s;derivative=N(derivative)
            require(n<80,'Local nilpotence bound failed')
        return out
    def multiply(a,b):
        out={}
        for u,c in a.items():
            for v,e in b.items():
                for z,k in mono(u,v).items():add(out,z,c*e*k)
        return out
    return mono,multiply

def differential(n,mono):
    source=cochains(n);target=cochains(n+1)
    cols={c:i for i,c in enumerate(source)};rows={c:i for i,c in enumerate(target)}
    mat=fmpq_mat(len(target),len(source));nnz_updates=0
    def put(row,col,val):
        nonlocal nnz_updates
        if val:
            i=rows[row];k=cols[col]
            mat[i,k]+=fmpq(val.numerator,val.denominator)
            nnz_updates+=1
    for chain in combinations(OBJECTS,n+2):
        pieces=[basis(chain[i+1]-chain[i]) for i in range(n+1)]
        for inputs in product(*pieces):
            tail=chain[1:];head=chain[:-1]
            for v in basis(tail[-1]-tail[0]):
                for out,c in mono(inputs[0],v).items():
                    put((chain,inputs,out),(tail,inputs[1:],v),c)
            for i in range(1,n+1):
                short=chain[:i]+chain[i+1:]
                for v,c in mono(inputs[i-1],inputs[i]).items():
                    short_inputs=inputs[:i-1]+(v,)+inputs[i+1:]
                    for out in basis(chain[-1]-chain[0]):
                        put((chain,inputs,out),(short,short_inputs,out),((-1)**i)*c)
            sign=(-1)**(n+1)
            for v in basis(head[-1]-head[0]):
                for out,c in mono(v,inputs[-1]).items():
                    put((chain,inputs,out),(head,inputs[:-1],v),sign*c)
    return mat,nnz_updates

def case(j,r,alpha,s):
    mono,mul=make_product(j,r,alpha,s)
    triples=0
    for chain in combinations(OBJECTS,4):
        for a,b,c in product(*(basis(chain[i+1]-chain[i]) for i in range(3))):
            require(mul(mono(a,b),{c:Q(1)})==mul({a:Q(1)},mono(b,c)),'Associativity')
            triples+=1
    unit_checks=0
    for n in range(5):
        for a in basis(n):
            require(mono(ZERO,a)==mono(a,ZERO)=={a:Q(1)},'Unit')
            unit_checks+=1
    d1,u1=differential(1,mono);d2,u2=differential(2,mono)
    require(d2*d1==fmpq_mat(d2.nrows(),d1.ncols()),'d2 d1 is nonzero')
    r1=d1.rank();r2=d2.rank()
    dimensions=(4,len(cochains(1)),len(cochains(2)),len(cochains(3)))
    require(dimensions==(4,620,1584,972),'Cochain dimensions')
    hh=(1,dimensions[1]-r1-3,dimensions[2]-r1-r2,dimensions[3]-r2)
    expected=(1,19,53,39) if s==0 else (1,1,35,39)
    require(hh==expected,'Unexpected Hochschild dimensions')
    require(r1==(598 if s==0 else 616) and r2==933,'Unexpected differential ranks')
    return {'j':j,'r':r,'alpha':str(alpha),'s':str(s),'cochain_dimensions':list(dimensions),
      'differential_ranks':[3,r1,r2],'hochschild_dimensions':list(hh),
      'associativity_triples':triples,'unit_checks':unit_checks,
      'd2_d1_zero':True,'d1_entries_accumulated':u1,'d2_entries_accumulated':u2}

def main():
    rows=[case(0,3,Q(-3,2),Q(0)),case(0,3,Q(-3,2),Q(1)),case(1,1,Q(-7,6),Q(1))]
    print(json.dumps({'version':35,'status':'PASS',
       'arithmetic':'Exact rational arithmetic: fractions.Fraction and python-flint fmpq_mat.',
       'multiplication':'Direct finite CGG product on commutative monomial vector spaces; path-order composition.',
       'scope':'The commutative corner and both nonzero m=3 CY corners. The all-parameter and hull assertions require the structural manuscript proof.',
       'cases':rows},indent=2,sort_keys=True))

if __name__=='__main__':main()
