#!/usr/bin/env python3
"""Independent cocycle-image rank audit, exact QQ; no quotient coordinates.

The v35 product/bar differential is reused as the defined algebra input.
The logarithm and cochain action are rebuilt here.  We compute
rank([d1, L ker(d2)]) - rank(d1), without taking quotient representatives.
"""
import sys,json,time,hashlib
from pathlib import Path
from functools import lru_cache
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from verify_quantum_vk_corner_v35 import basis,cochains,differential,make_product,Q,require,fmpq,fmpq_mat

def rat(x):return fmpq(x.numerator,x.denominator)
def addto(p,u,c):
    p[u]=p.get(u,Q(0))+c
    if not p[u]:del p[u]

def N_on_mono(u,j):
    x,y,z,w=u;p={}
    if y:addto(p,(x+1,y-1,z,w),Q(y))
    if z:addto(p,(x,y+1,z-1,w),Q(2*z))
    if w:
        if j==0:addto(p,(x,y,z+3,w-1),Q(-w))
        else:
            addto(p,(x+1,y,z+2,w-1),Q(-w))
            addto(p,(x,y+2,z+1,w-1),Q(w))
    return p

def delta_factory(j):
    @lru_cache(None)
    def delta(u):
        p=N_on_mono(u,j);out={};k=1
        while p:
            for v,a in p.items():addto(out,v,a*Q((-1)**(k+1),k))
            q={}
            for v,a in p.items():
                for z,b in N_on_mono(v,j).items():addto(q,z,a*b)
            p=q;k+=1
        return out
    return delta

def nullspace(A):
    R,r=A.rref();piv=[]
    for i in range(r):piv.append(next(k for k in range(R.ncols()) if R[i,k]))
    free=[k for k in range(A.ncols()) if k not in set(piv)]
    K=fmpq_mat(A.ncols(),len(free))
    for k,f in enumerate(free):
        K[f,k]=1
        for i,p in enumerate(piv):K[p,k]=-R[i,f]
    require(A*K==fmpq_mat(A.nrows(),len(free)),'full kernel')
    return K,r

def cochain_action_on_columns(n,delta,K):
    """Evaluate L f on all input tuples, independently of elementary-column action."""
    cs=cochains(n);idx={c:i for i,c in enumerate(cs)}
    out=fmpq_mat(len(cs),K.ncols())
    # First collect nonzero sparse K rows.
    rows=[[(k,K[i,k]) for k in range(K.ncols()) if K[i,k]] for i in range(K.nrows())]
    outs={degree:{v:[] for v in basis(degree)} for degree in range(5)}
    for degree in outs:
        for u in basis(degree):
            for v,a in delta(u).items():outs[degree][v].append((u,rat(a)))
    for dest,(chain,inputs,result) in enumerate(cs):
        totaldeg=chain[-1]-chain[0]
        for u,a in outs[totaldeg][result]:
            source=idx[(chain,inputs,u)]
            for k,v in rows[source]:out[dest,k]+=a*v
        for pos,u in enumerate(inputs):
            for v,a in delta(u).items():
                newinputs=inputs[:pos]+(v,)+inputs[pos+1:]
                source=idx[(chain,newinputs,result)]
                for k,b in rows[source]:out[dest,k]-=rat(a)*b
    return out

def hjoin(A,B):
    return fmpq_mat([[A[i,k] for k in range(A.ncols())]+[B[i,k] for k in range(B.ncols())] for i in range(A.nrows())])

def case(j):
    start=time.time();mono,_=make_product(j,3-2*j,Q(0),Q(1))
    d1,_=differential(1,mono);d2,_=differential(2,mono)
    K,r2=nullspace(d2)
    print('kernel',j,K.nrows(),K.ncols(),time.time()-start,file=sys.stderr,flush=True)
    LZ=cochain_action_on_columns(2,delta_factory(j),K)
    require(d2*LZ==fmpq_mat(d2.nrows(),K.ncols()),'preserve cocycles')
    r1=d1.rank();fullrank=hjoin(d1,LZ).rank();rank=fullrank-r1
    require((r1,r2)==(616,933),'differential ranks')
    require(rank==[31,29][j],'first Gerstenhaber rank')
    return {'j':j,'r':3-2*j,'full_cocycle_dimension':K.ncols(),
      'boundary_rank':r1,'d2_rank':r2,'rank_boundary_and_derivative_cocycles':fullrank,
      'intrinsic_HH2_action_rank':rank,'HH2_dimension':K.ncols()-r1,
      'action_preserves_cocycles':True,'algorithm':'rank([d1,L ker(d2)])-rank(d1)',
      'elapsed_seconds':round(time.time()-start,3)}

if __name__=='__main__':
    data={'status':'PASS','arithmetic':'QQ exactly via fmpq_mat','independent_of':'quotient-coordinate construction in explore_hh_action.py',
      'cases':[case(j) for j in (0,1)]}
    print(json.dumps(data,indent=2,sort_keys=True))
