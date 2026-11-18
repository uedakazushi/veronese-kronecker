#!/usr/bin/env python3
"""Quadratic equations for the outer-derivation jump locus of quantum VK.

Read-only computation on the frozen v36 product. All arithmetic is rational.
The output is the canonical map Sym^2 ker(L_delta|HH2) -> coker(L_delta|HH2)
in explicit choices of bases, together with the lifting and cocycle checks.
"""
from pathlib import Path
import sys,json,time
CODE=Path(__file__).resolve().parent
if not (CODE/'verify_vk_gerstenhaber_v36.py').is_file():
    CODE=CODE.parent/'output/vk_lo_deformations_v36/code'
sys.path.insert(0,str(CODE))
from verify_vk_gerstenhaber_v36 import *

def log(s):print(s,file=sys.stderr,flush=True)
def zero(n,m):return fmpq_mat(n,m)
def nullbasis(M):
    R,r=M.rref();p=pivots(R,r);free=[i for i in range(M.ncols()) if i not in set(p)]
    K=zero(M.ncols(),len(free))
    for c,j in enumerate(free):
        K[j,c]=1
        for i,k in enumerate(p):K[k,c]=-R[i,j]
    require(M*K==zero(M.nrows(),len(free)),'nullspace')
    return K
def cochain_dict(n,V,c=0):
    D={}
    for i,(chain,ins,out) in enumerate(cochains(n)):
        if V[i,c]:D.setdefault((chain,ins),{})[out]=V[i,c]
    return D
def accum(D,k,v):
    if v:
        D[k]=D.get(k,fmpq(0))+v
        if not D[k]:del D[k]
def compose22(F,G):
    rows={v:i for i,v in enumerate(cochains(3))};out=zero(len(rows),1)
    for chain in combinations(OBJECTS,4):
        for a,b,c in product(*(basis(chain[i+1]-chain[i]) for i in range(3))):
            poly={}
            for v,s in G.get((chain[:3],(a,b)),{}).items():
                for w,t in F.get(((chain[0],chain[2],chain[3]),(v,c)),{}).items():accum(poly,w,s*t)
            for v,s in G.get((chain[1:],(b,c)),{}).items():
                for w,t in F.get(((chain[0],chain[1],chain[3]),(a,v)),{}).items():accum(poly,w,-s*t)
            for w,s in poly.items():out[rows[(chain,(a,b,c),w)],0]=s
    return out
def act12(D,F):
    rows={v:i for i,v in enumerate(cochains(2))};out=zero(len(rows),1)
    for chain in combinations(OBJECTS,3):
        for a,b in product(*(basis(chain[i+1]-chain[i]) for i in range(2))):
            poly={}
            for v,s in F.get((chain,(a,b)),{}).items():
                for w,t in D.get(((chain[0],chain[2]),(v,)),{}).items():accum(poly,w,s*t)
            for v,s in D.get((chain[:2],(a,)),{}).items():
                for w,t in F.get((chain,(v,b)),{}).items():accum(poly,w,-s*t)
            for v,s in D.get((chain[1:],(b,)),{}).items():
                for w,t in F.get((chain,(a,v)),{}).items():accum(poly,w,-s*t)
            for w,s in poly.items():out[rows[(chain,(a,b),w)],0]=s
    return out
def concat(Vs):
    return fmpq_mat([[V[i,0] for V in Vs] for i in range(Vs[0].nrows())])
def asjson(M):return [[str(M[i,j]) for j in range(M.ncols())] for i in range(M.nrows())]

def compute(j):
    start=time.time();r=3-2*j
    mono,mul=make_product(j,r,Q(0),Q(1));delta=derivation(j,r)
    d1,_=differential(1,mono);d2,_=differential(2,mono);L=action(2,delta)
    require(d1.rank()==616 and d2.rank()==933,'frozen differential ranks')
    R,b=d1.transpose().rref();ps=pivots(R,b);fs=[i for i in range(d1.nrows()) if i not in set(ps)]
    df=select(d2,range(d2.nrows()),fs)
    Z,zr=df.rref();zp=pivots(Z,zr);zf=[i for i in range(len(fs)) if i not in set(zp)]
    V=zero(len(fs),len(zf))
    for k,c in enumerate(zf):
        V[c,k]=1
        for i,p in enumerate(zp):V[p,k]=-Z[i,c]
    Uall=zero(d1.nrows(),len(zf))
    for i,f in enumerate(fs):
        for k in range(len(zf)):Uall[f,k]=V[i,k]
    Rfree=select(R,range(b),fs).transpose()
    def hclass(W):
        Wf=select(W,fs,range(W.ncols()))-Rfree*select(W,ps,range(W.ncols()))
        H=select(Wf,zf,range(W.ncols()))
        require(Wf==V*H,'cochain is not a cocycle')
        return H
    H=hclass(L*Uall);K=nullbasis(H);U=Uall*K;k=K.ncols()
    require(k==4+2*j,'invariant tangent dimension')
    log(f'j{j} cohomology ready {time.time()-start:.2f}s')
    # Solve first-order derivation lift d1 eta = L_delta u.
    D1R,rank=d1.rref();pc=pivots(D1R,rank)
    B1=select(d1,ps,pc);rhs=L*U
    etasmall=B1.solve(select(rhs,ps,range(k)))
    Eta=zero(d1.ncols(),k)
    for i,c in enumerate(pc):
        for z in range(k):Eta[c,z]=etasmall[i,z]
    require(d1*Eta==rhs,'first-order derivation lift')
    # Solve second-order associativity d2 v = u circle u.
    Us=[cochain_dict(2,U,i) for i in range(k)]
    Es=[cochain_dict(1,Eta,i) for i in range(k)]
    pairs=list(combinations(range(k),2))+[(i,i) for i in range(k)]
    pairs=sorted(pairs)
    Rs=[]
    for i,l in pairs:
        rr=compose22(Us[i],Us[l])
        if i!=l:rr+=compose22(Us[l],Us[i])
        Rs.append(rr)
    RHS=concat(Rs)
    D2T,rank=d2.transpose().rref();pr=pivots(D2T,rank);cs=[fs[z] for z in zp]
    B2=select(d2,pr,cs)
    vsmall=B2.solve(select(RHS,pr,range(len(pairs))))
    Vs=zero(d2.ncols(),len(pairs))
    for i,c in enumerate(cs):
        for z in range(len(pairs)):Vs[c,z]=vsmall[i,z]
    require(d2*Vs==RHS,'second-order associativity')
    log(f'j{j} lifts ready {time.time()-start:.2f}s')
    Obs=L*Vs
    for c,(i,l) in enumerate(pairs):
        a=act12(Es[i],Us[l])
        if i!=l:a+=act12(Es[l],Us[i])
        for n in range(Obs.nrows()):Obs[n,c]+=a[n,0]
    require(d2*Obs==zero(d2.nrows(),len(pairs)),'second-order symmetry obstruction cocycle')
    O=hclass(Obs)
    HR,hr=H.transpose().rref();hp=pivots(HR,hr);hf=[i for i in range(H.nrows()) if i not in set(hp)]
    QO=select(O,hf,range(O.ncols()))-select(HR,range(hr),hf).transpose()*select(O,hp,range(O.ncols()))
    require(QO.nrows()==k,'cokernel dimension')
    log(f'j{j} quadratic rank {QO.rank()}, complete {time.time()-start:.2f}s')
    KC=select(K,hf,range(k))-select(HR,range(hr),hf).transpose()*select(K,hp,range(k))
    require(QO.rank()==j,'published quadratic rank')
    require(KC.rank()==j,'published kernel-to-cokernel rank')
    nonzero_pairs=[list(pairs[c]) for c in range(len(pairs)) if any(QO[i,c] for i in range(k))]
    nonzero_kernel_columns=[c for c in range(k) if any(KC[i,c] for i in range(k))]
    require(nonzero_pairs==([] if j==0 else [[5,5]]),'published square support')
    require(nonzero_kernel_columns==([] if j==0 else [5]),'canonical hyperplane support')
    return {'j':j,'r':r,'invariant_dimension':k,'pairs':pairs,'quadratic_obstruction_matrix':asjson(QO),'quadratic_rank':QO.rank(),'HH2_matrix':asjson(H),'kernel_basis':asjson(K),'kernel_to_cokernel_matrix':asjson(KC),'cokernel_free_coordinates':hf,'first_order_cocycles':asjson(U),'first_order_derivation_lifts':asjson(Eta),'checks':{'first_order_derivation_lifts':True,'second_order_associativity':True,'second_order_symmetry_cocycles':True}}

if __name__=='__main__':
    rows=[compute(j) for j in [0,1]]
    actual=json.loads(json.dumps({'version':37,'status':'PASS','arithmetic':'QQ','scope':'Canonical quadratic obstruction on outer-derivation jump locus; the full formal jump ideal is not computed.','cases':rows}))
    expected=json.loads(Path(__file__).with_name('vk_symmetry_v37_certificate.json').read_text())
    require(actual==expected,'complete frozen rational certificate')
    print(json.dumps(actual,indent=2))
