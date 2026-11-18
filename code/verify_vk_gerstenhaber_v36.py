#!/usr/bin/env python3
"""Exact rational Gerstenhaber HH1-module invariant of two CGG VK corners.

Normal execution is read-only. It constructs the cochain complex from the
finite CGG product, proves the logarithm is a derivation on every relevant
input pair, checks chain maps, constructs quotient representatives, then
computes all nilpotent power ranks. A frozen JSON certificate is compared by
verify_v36.py. Historical multiplication implementation remains unchanged.
"""
import sys,json,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify_quantum_vk_corner_v35 import *

def tell(*a): pass

def select(M,rs,cs):
    return fmpq_mat([[M[i,k] for k in cs] for i in rs])

def pivots(R,rank):
    return [next(k for k in range(R.ncols()) if R[i,k]) for i in range(rank)]

def derivation(j,r):
    P={(0,0,r,0):Q(1)} if j==0 else {(1,0,r+1,0):Q(1),(0,2,r,0):Q(-1)}
    fields=[{}, {(1,0,0,0):Q(1)}, {(0,1,0,0):Q(2)}, {u:-c for u,c in P.items()}]
    def N(poly):
        out={}
        for u,c in poly.items():
            for i,v in enumerate(u):
                if not v:continue
                z=list(u);z[i]-=1
                for f,e in fields[i].items():add(out,plus(tuple(z),f),c*v*e)
        return out
    @lru_cache(None)
    def delta(u):
        p=N({u:Q(1)});out={};n=1
        while p:
            for v,c in p.items():add(out,v,c*Q((-1)**(n+1),n))
            p=N(p);n+=1
        return out
    return delta

def action(n,delta):
    coords=cochains(n);lookup={c:i for i,c in enumerate(coords)}
    L=fmpq_mat(len(coords),len(coords))
    inv={}
    for deg in range(5):
        inv[deg]={m:[] for m in basis(deg)}
        for m in basis(deg):
            for out,c in delta(m).items():inv[deg][out].append((m,c))
    for col,(chain,inputs,out) in enumerate(coords):
        for v,c in delta(out).items():
            L[lookup[(chain,inputs,v)],col]+=fmpq(c.numerator,c.denominator)
        for k,a in enumerate(inputs):
            for v,c in inv[chain[k+1]-chain[k]][a]:
                args=inputs[:k]+(v,)+inputs[k+1:]
                L[lookup[(chain,args,out)],col]-=fmpq(c.numerator,c.denominator)
    return L

def jordan(M):
    n=M.nrows();power=fmpq_mat(n,n)
    for i in range(n):power[i,i]=1
    ranks=[n]
    for k in range(1,n+2):
        power=power*M;r=power.rank();ranks.append(r)
        if r==0:break
    require(ranks[-1]==0,'not nilpotent')
    ranks.append(0)
    blocks=[]
    for k in range(1,len(ranks)-1):
        count=ranks[k-1]-2*ranks[k]+ranks[k+1]
        blocks.extend([k]*count)
    return {'ranks':ranks[:-1],'blocks':sorted(blocks,reverse=True)}

def case_action(j,r):
    t=time.time();tell('case',j,r)
    mono,mul=make_product(j,r,Q(0),Q(1));delta=derivation(j,r)
    def dp(p):
        out={}
        for u,c in p.items():
            for v,d in delta(u).items():add(out,v,c*d)
        return out
    for a_deg in range(1,4):
        for b_deg in range(1,5-a_deg):
            for a,b in product(basis(a_deg),basis(b_deg)):
                lhs=dp(mono(a,b));rhs=mul(delta(a),{b:Q(1)})
                for v,c in mul({a:Q(1)},delta(b)).items():add(rhs,v,c)
                require(lhs==rhs,'not derivation')
    d1,_=differential(1,mono);d2,_=differential(2,mono)
    require(d2*d1==fmpq_mat(d2.nrows(),d1.ncols()),'d2 d1')
    require(d1.rank()==616 and d2.rank()==933,'Hochschild differential ranks')
    delta_vec=fmpq_mat(len(cochains(1)),1)
    for k,(chain,ins,out) in enumerate(cochains(1)):
        v=delta(ins[0]).get(out,Q(0))
        delta_vec[k,0]=fmpq(v.numerator,v.denominator)
    require(d1*delta_vec==fmpq_mat(d1.nrows(),1),'delta is a cocycle')
    require(delta((0,1,0,0))=={(1,0,0,0):Q(1)},'delta non-inner arrow witness')
    tell('differentials',time.time()-t)
    R,b=d1.transpose().rref();ps=pivots(R,b);fs=[i for i in range(d1.nrows()) if i not in set(ps)]
    tell('boundary reduced',b,len(fs),time.time()-t)
    df=select(d2,range(d2.nrows()),fs)
    Z,zr=df.rref();zp=pivots(Z,zr);zf=[i for i in range(len(fs)) if i not in set(zp)]
    V=fmpq_mat(len(fs),len(zf))
    for k,c in enumerate(zf):
        V[c,k]=1
        for i,p in enumerate(zp):V[p,k]=-Z[i,c]
    require(df*V==fmpq_mat(d2.nrows(),len(zf)),'kernel construction')
    tell('kernel',len(zf),time.time()-t)
    L=action(2,delta);L1=action(1,delta)
    require(L*d1==d1*L1,'degree1-2 chain map')
    W=select(L,range(L.nrows()),fs)*V
    Wf=select(W,fs,range(W.ncols()))-select(R,range(b),fs).transpose()*select(W,ps,range(W.ncols()))
    H=select(Wf,zf,range(W.ncols()))
    require(Wf==V*H,'cohomology invariance')
    hh2=jordan(H);tell('HH2',hh2,time.time()-t)
    R3,b3=d2.transpose().rref();p3=pivots(R3,b3);f3=[i for i in range(d2.nrows()) if i not in set(p3)]
    L3=action(3,delta)
    require(L3*d2==d2*L,'degree2-3 chain map')
    H3=select(L3,f3,f3)-select(R3,range(b3),f3).transpose()*select(L3,p3,f3)
    hh3=jordan(H3);tell('HH3',hh3,time.time()-t)
    return {'j':j,'r':r,'alpha':'0','s':'1','cochain_dimensions':[4,620,1584,972],'differential_ranks':[3,616,933],'chain_maps_verified':True,'derivation_all_relevant_pairs':True,'non_inner_arrow_witness':'delta(y)=x','HH2':hh2,'HH3':hh3,'HH2_matrix':[[str(H[i,k]) for k in range(H.ncols())] for i in range(H.nrows())],'HH3_matrix':[[str(H3[i,k]) for k in range(H3.ncols())] for i in range(H3.nrows())]}

if __name__=='__main__':
    rows=[case_action(j,3-2*j) for j in [0,1]]
    require(rows[0]['HH2']['blocks']==[13,10,7,5],'HH2 first partition')
    require(rows[1]['HH2']['blocks']==[11,9,6,5,3,1],'HH2 second partition')
    require(rows[0]['HH3']['blocks']==[14,11,8,5,1],'HH3 first partition')
    require(rows[1]['HH3']['blocks']==[13,10,7,5,3,1],'HH3 second partition')
    print(json.dumps({'version':36,'status':'PASS',
      'arithmetic':'Exact rational arithmetic: Fraction and python-flint fmpq_mat',
      'scope':'Fixed m=3 CGG corners; general alpha and nonzero s follow by explicit idempotent-preserving isomorphisms.',
      'method':'Boundary-pivot quotient and exact nilpotent power ranks; degree1-2 and degree2-3 chain maps checked.',
      'cases':rows},indent=2,sort_keys=True))
