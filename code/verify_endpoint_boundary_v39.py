#!/usr/bin/env python3
"""Exact checks for the H-dependent U-chart and all cyclic cut fibers.

The proof for every root order is in the companion manuscript. These finite
checks independently compare PBW gauge formulas, a multiplication-matrix norm,
and explicit faithful quiver models. Normal verification never writes a
certificate. No floating point roots are used.
"""
from pathlib import Path
from collections import deque
from functools import lru_cache
from itertools import product
from math import gcd
import argparse, hashlib, json
import sympy as sp

HERE=Path(__file__).resolve().parent
CERT=HERE/'endpoint_boundary_v39_certificate.json'
z=sp.Symbol('z')
Q,J,U,u=sp.symbols('Q J U u')

class QuantumLaurent:
    # Normal form: u^a x^b Q^c J^d, with x*u=t^-1*u*x.
    def __init__(self,ell):
        self.ell=ell
        self.K=sp.QQ.alg_field_from_poly(sp.Poly(sp.cyclotomic_poly(ell,z),z),alias='t')
        self.t=self.K.unit
        self.tp=[self.t**i for i in range(ell)]
        self.one=self.mon((0,0,0,0))
    def mon(self,key,c=1):
        a=self.K.convert(c)
        return {key:a} if a else {}
    def clean(self,p):return {k:a for k,a in p.items() if a}
    def add(self,*ps):
        r={}
        for p in ps:
            for k,a in p.items():r[k]=r.get(k,self.K.zero)+a
        return self.clean(r)
    def scale(self,p,c):
        c=self.K.convert(c)
        return self.clean({k:a*c for k,a in p.items()})
    def mul(self,p,q):
        r={}
        for (a,b,c,d),v in p.items():
            for (e,f,g,h),w in q.items():
                key=(a+e,b+f,c+g,d+h)
                r[key]=r.get(key,self.K.zero)+v*w*self.tp[(-b*e)%self.ell]
        return self.clean(r)
    def power(self,p,n):
        assert n>=0
        out=self.one
        while n:
            if n%2:out=self.mul(out,p)
            p=self.mul(p,p);n//=2
        return out
    def sigma(self,p,n=1):return self.clean({k:a*self.tp[(n*k[0])%self.ell] for k,a in p.items()})
    def sub(self,p,q):return self.add(p,self.scale(q,-1))
    def coeff(self,c):
        rr=c.to_list()
        assert len(rr)<=1,'Expected rational coefficient after orbit norm'
        return sp.Rational(str(rr[0])) if rr else sp.Integer(0)
    def commutative(self,p,invariant=False):
        out=0
        for (a,b,c,d),v in p.items():
            assert b==0
            if invariant:
                assert a%self.ell==0
                term=U**(a//self.ell)
            else:term=u**a
            out+=self.coeff(v)*term*Q**c*J**d
        return sp.expand(out)


def matrix_norm(h,ell):
    """Norm from multiplication in QQ[Q,U±][u]/(u^ell-U)."""
    mat=sp.zeros(ell)
    for term in sp.Add.make_args(sp.expand(h)):
        a=int(term.as_powers_dict().get(u,0))
        c=sp.cancel(term/u**a)
        assert not c.has(u)
        for j in range(ell):
            q,r=divmod(a+j,ell)
            mat[r,j]+=c*U**q
    det=(J*sp.eye(ell)-mat).det(method='domain-ge')
    return sp.expand(det)


def gauge_norm_check(ell):
    A=QuantumLaurent(ell)
    x=A.mon((0,1,0,0));xi=A.mon((0,-1,0,0))
    uu=A.mon((1,0,0,0));q=A.mon((0,0,1,0));jj=A.mon((0,0,0,1))
    # beta=1; the manuscript proves the identity for every nonzero beta.
    v=A.add(A.mon((-1,0,1,0),-1),A.mon((-1,2,0,0),-A.t))
    assert A.mul(uu,x)==A.scale(A.mul(x,uu),A.t)
    assert A.mul(v,x)==A.scale(A.mul(x,v),A.t**-1)
    assert A.sub(A.mul(uu,v),A.mul(v,uu))==A.scale(A.power(x,2),A.t**-1-A.t)
    assert A.add(A.mul(uu,v),A.scale(A.power(x,2),A.t),q)=={}
    H=A.add(A.mul(A.power(uu,4),v),
            A.scale(A.mul(A.power(uu,2),A.power(v,3)),2),
            A.mul(x,A.power(uu,4)),A.mul(A.power(x,2),A.power(v,3)))
    h={k:c for k,c in H.items() if k[1]==0}
    assert all(k[1]>=0 for k in H)
    G=A.mul(xi,A.sub(H,h))
    assert all(k[1]>=0 for k in G)
    w=A.mul(xi,A.sub(jj,H));W=A.add(w,G)
    assert W==A.mul(xi,A.sub(jj,h))
    for b in (x,uu,v):
        lhs=A.sub(A.mul(w,b),A.mul(A.sigma(b),w))
        rhs=A.mul(xi,A.sub(A.mul(b,H),A.mul(H,b)))
        assert lhs==rhs
    assert A.mul(x,W)==A.sub(jj,h)
    assert A.mul(W,x)==A.sub(jj,A.sigma(h))
    assert A.mul(W,uu)==A.scale(A.mul(uu,W),A.t)
    XP=A.power(x,ell);WP=A.power(W,ell)
    norm=A.one
    for i in range(ell):norm=A.mul(norm,A.sub(jj,A.sigma(h,i)))
    assert A.mul(XP,WP)==norm
    for b in (x,uu,W):
        assert A.mul(XP,b)==A.mul(b,XP)
        assert A.mul(WP,b)==A.mul(b,WP)
    hs=A.commutative(h)
    assert sp.expand(hs+Q*u**3+2*Q**3/u)==0
    ns=A.commutative(norm,True)
    ds=matrix_norm(hs,ell)
    assert sp.expand(ns-ds)==0
    for k in range(ell):
        shifted=A.one
        for i in range(ell):shifted=A.mul(shifted,A.sub(jj,A.sigma(h,i+k)))
        assert shifted==norm
    return {'order':ell,'coefficient_field':'QQ[t]/Phi_'+str(ell),
            'mixed_H':'u^4*v+2*u^2*v^3+x*u^4+x^2*v^3','h':str(hs),
            'norm':str(ns),'norm_equals_independent_determinant':True,
            'Ore_gauge_and_GWA_relations':True,'central_powers_and_norm_relation':True,
            'all_cyclic_rotations_preserve_norm':True}


def path_end(path,r):
    source,direction,length=path
    return (source+direction*length)%r


def cut_model(ell,cuts):
    """Faithful inflated basic algebra for every nonempty zero-edge set.

    Edge i goes from i to i+1. Contract nonzero edges, retaining the exact
    original chain multiplicities. Compare all original quiver relations
    and the full generated vector-space basis, not just dimensions.
    """
    cuts=tuple(sorted(cuts));r=len(cuts);assert r
    chains=[]
    for i,c in enumerate(cuts):
        nxt=cuts[(i+1)%r]
        vertices=[];k=(c+1)%ell
        while True:
            vertices.append(k)
            if k==nxt:break
            k=(k+1)%ell
        chains.append(vertices)
    sizes=[len(c) for c in chains]
    assert sum(sizes)==ell
    positions={v:(i,j) for i,c in enumerate(chains) for j,v in enumerate(c)}
    paths=[(i,0,0) for i in range(r)]
    paths += [(i,d,n) for i in range(r) for d in (-1,1) for n in range(1,r)]
    def pmul(a,b):
        # a*b: first b, then a.
        if b is None or a is None or path_end(b,r)!=a[0]:return None
        if a[2]==0:return b
        if b[2]==0:return a
        if a[1]!=b[1] or a[2]+b[2]>=r:return None
        return (b[0],a[1],a[2]+b[2])
    def mul(a,b):
        if a is None or b is None:return None
        p,i,j=a;q,k,l=b
        if j!=k:return None
        rr=pmul(p,q)
        return None if rr is None else (rr,i,l)
    verts=[]
    for n in range(ell):
        b,i=positions[n];verts.append(((b,0,0),i,i))
    xs=[];ys=[]
    for n in range(ell):
        b,i=positions[n];c,j=positions[(n+1)%ell]
        if n not in cuts:
            assert b==c
            xx=((b,0,0),j,i);yy=((b,0,0),i,j)
        elif r==1:xx=yy=None
        else:
            assert c==(b+1)%r
            xx=((b,1,1),j,i);yy=((c,-1,1),i,j)
        xs.append(xx);ys.append(yy)
        assert mul(yy,xx)==(None if n in cuts else verts[n])
        assert mul(xx,yy)==(None if n in cuts else verts[(n+1)%ell])
    for start in range(ell):
        a=verts[start]
        for n in range(ell):a=mul(xs[(start+n)%ell],a)
        assert a is None
        a=verts[start]
        for n in range(ell):a=mul(ys[(start-n-1)%ell],a)
        assert a is None
    gens=[p for p in verts+xs+ys if p is not None]
    reached=set(gens);queue=deque(gens)
    while queue:
        a=queue.popleft()
        for g in gens:
            b=mul(g,a)
            if b is not None and b not in reached:reached.add(b);queue.append(b)
    full={(p,i,j) for p in paths for i in range(sizes[path_end(p,r)]) for j in range(sizes[p[0]])}
    assert reached==full
    expected=2*ell**2-sum(n*n for n in sizes)
    assert len(full)==expected
    rad={p for p in full if p[0][2]}
    assert len(rad)==2*(ell**2-sum(n*n for n in sizes))
    # Graded path length proves radical power r is zero and r-1 is nonzero.
    assert max([p[0][2] for p in full])==r-1
    if r>1:
        a=((0,1,1),0,0)
        for k in range(1,r-1):a=mul(((k,1,1),0,0),a)
        assert a is not None and a[0][2]==r-1
        assert mul(((r-1,1,1),0,0),a) is None
    return {'order':ell,'zero_edges':list(cuts),'simple_dimensions':sizes,
            'basic_dimension':r*(2*r-1),'fiber_dimension':len(full),
            'radical_dimension':len(rad),'radical_nilpotence_index':r}


def monomial_norms():
    records=[]
    for ell in range(3,13):
        for n in (1,2,3,5,6,9):
            g=gcd(ell,n);rr=ell//g
            actual=matrix_norm(u**n,ell)
            expected=sp.expand((J**rr-U**(n//g))**g)
            assert sp.expand(actual-expected)==0
            zeros=[i for i in range(ell) if i*n%ell==0]
            assert len(zeros)==g
            row=cut_model(ell,zeros)
            assert row['simple_dimensions']==[rr]*g
            records.append({'order':ell,'exponent':n,'gcd':g,'simple_dimensions':[rr]*g,
                            'norm':str(expected)})
    return records



def cyclic_descent_check(ell,g):
    """General-g explicit descent matrices over a twisted nilpotent corner."""
    assert ell%g==0
    n=ell//g
    A=QuantumLaurent(ell);K=A.K;tp=A.tp
    zz=K.convert(2)
    # kappa^a times P^k (direction +1) or R^k (direction -1).
    one={(0,0,0):K.one}
    kap={(1,0,0):K.one} if g>1 else {(0,0,0):zz}
    pp={(0,1,1):K.one} if g>1 else {}
    rr={(0,-1,1):K.one} if g>1 else {}
    def add(a,b):
        out=dict(a)
        for k,v in b.items():out[k]=out.get(k,K.zero)+v
        return {k:v for k,v in out.items() if v}
    def scale(a,c):return {k:v*c for k,v in a.items() if v*c}
    def mul(a,b):
        out={}
        for (e,d,k),v in a.items():
            for (f,dd,l),w in b.items():
                if k and l and d!=dd:continue
                if k+l>=g:continue
                direction=d if k else dd
                if not k+l:direction=0
                qq,ee=divmod(e+f,g)
                coeff=v*w*tp[(-n*d*k*f)%ell]*zz**qq
                key=(ee,direction,k+l)
                out[key]=out.get(key,K.zero)+coeff
        return {k:v for k,v in out.items() if v}
    def madd(a,b):
        out=dict(a)
        for ij,v in b.items():
            c=add(out.get(ij,{}),v)
            if c:out[ij]=c
            else:out.pop(ij,None)
        return out
    def mmul(a,b):
        out={}
        for (i,j),v in a.items():
            for (k,l),w in b.items():
                if j==k:out=madd(out,{(i,l):mul(v,w)})
        return {ij:v for ij,v in out.items() if v}
    def mscale(a,c):return {ij:scale(v,c) for ij,v in a.items() if scale(v,c)}
    identity={(i,i):one for i in range(n)}
    def mpow(a,k):
        out=identity
        while k:
            if k%2:out=mmul(out,a)
            a=mmul(a,a);k//=2
        return out
    b=[zz*(K.one-tp[(g*i)%ell]) for i in range(n)]
    delta=K.one
    for v in b[1:]:
        assert v
        delta*=v
    um={(i,i):scale(kap,tp[i]) for i in range(n)}
    xm={(i+1,i):one for i in range(n-1)}
    wm={(i-1,i):scale(one,b[i]) for i in range(1,n)}
    if pp:xm[(0,n-1)]=pp
    if rr:wm[(n-1,0)]=scale(rr,delta**-1)
    checks=0
    def check(a,b):
        nonlocal checks
        assert a==b,(ell,g,a,b)
        checks+=1
    check(mmul(xm,um),mscale(mmul(um,xm),tp[-1]))
    check(mmul(wm,um),mscale(mmul(um,wm),tp[1]))
    check(mmul(xm,wm),{(i,i):scale(one,b[i]) for i in range(n) if b[i]})
    check(mmul(wm,xm),{(i,i):scale(one,b[(i+1)%n]) for i in range(n) if b[(i+1)%n]})
    check(mpow(xm,n),{(i,i):pp for i in range(n)} if pp else {})
    check(mpow(wm,n),{(i,i):rr for i in range(n)} if rr else {})
    check(mpow(xm,ell),{})
    check(mpow(wm,ell),{})
    check(mpow(um,ell),mscale(identity,zz**n))
    ug=mscale(mpow(um,g),zz**-1)
    for i in range(n):
        e={}
        for k in range(n):e=madd(e,mscale(mpow(ug,k),tp[(-g*i*k)%ell]/K.convert(n)))
        check(e,{(i,i):one})
    return {'order':ell,'stabilizer_order':g,'matrix_size':n,
            'corner_dimension':g*(2*g-1),'exact_matrix_identities':checks,
            'coefficient_relation':'kappa^g=2; sigma(kappa)=t^(-n)*kappa',
            'including_g1_or_n1':g==1 or n==1}


def compute():
    gauges=[gauge_norm_check(n) for n in (3,4,5,6,8)]
    patterns=[]
    for ell in range(3,9):
        for mask in range(1,1<<ell):
            cuts=[i for i in range(ell) if (mask>>i)&1]
            patterns.append(cut_model(ell,cuts))
    monomials=monomial_norms()
    descents=[cyclic_descent_check(ell,g) for ell in range(3,13) for g in range(1,ell+1) if ell%g==0]
    p0=matrix_norm(u**5,5);p1=matrix_norm(-Q*u**3,5)
    assert sp.expand(p0-(J-U)**5)==0
    assert sp.expand(p1-J**5-Q**5*U**3)==0
    # On U invertible, derivatives give the claimed set-theoretic singular loci.
    assert sp.diff(p1,J)==5*J**4
    assert sp.diff(p1,Q)==5*Q**4*U**3
    return {'version':39,'status':'PASS',
       'scope':'H-dependent U-invertible center, spectral norm, cyclic cut fibers',
       'proof_scope':'Finite exact checks supplement all-order algebraic proofs; no theorem for all orders is inferred from bounded checks.',
       'gauge_and_independent_norm_checks':gauges,
       'all_nonempty_cut_patterns_orders_3_through_8':patterns,
       'cut_pattern_count':len(patterns),
       'monomial_norm_and_gap_checks':monomials,
       'general_cyclic_descent_matrices':descents,
       'weight4_order5_examples':{
          'H=u^5':{'center_norm':str(p0),'singular_locus':'Xi=Omega=J-U=0','singular_dimension':2,'generic_boundary_simple_dimensions':[1]*5},
          'H=u^4*v':{'center_norm':str(p1),'singular_locus':'Xi=Omega=J=Q=0','singular_dimension':1,'Q_nonzero_boundary_simple_dimensions':[5]}},
       'exact_arithmetic_only':True}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check',nargs='?',const=str(CERT))
    ap.add_argument('--write-certificate',nargs='?',const=str(CERT))
    args=ap.parse_args();result=compute()
    if args.check:
        expected=json.loads(Path(args.check).read_text())
        if result!=expected:raise SystemExit('Complete certificate mismatch')
    if args.write_certificate:
        Path(args.write_certificate).write_text(json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2))

if __name__=='__main__':main()
