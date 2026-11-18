#!/usr/bin/env python3
"""Exact structural checks for full formal cyclic descent and residue charts.

The manuscript proves all orders. This program tests the noncommutative matrix
identities over a rational function field, with independent unit edge weights.
It does not replace a proof of the Brauer residue theorem by finite samples.
Normal execution only reads its fixed certificate.
"""
from pathlib import Path
from math import gcd
import argparse,json
import sympy as sp

HERE=Path(__file__).resolve().parent
CERT=HERE/'boundary_ramification_v40_certificate.json'

def formal_model(ell,g):
    n=ell//g
    zz=sp.Symbol('zz'); tt=sp.Symbol('tt')
    kk=sp.QQ.alg_field_from_poly(sp.Poly(sp.cyclotomic_poly(ell,tt),tt),alias='t')
    bs=sp.symbols('b1:'+str(n))
    F=kk.frac_field(zz,*bs)
    t=F.convert(kk.unit,kk); z=F.convert(zz)
    tp=[t**i for i in range(ell)]
    def mon(k,c=1):
        c=F.convert(c)
        return {k:c} if c else {}
    one=mon((0,0,0)); P=mon((0,1,0)); R=mon((0,0,1))
    kap=mon((1,0,0)) if g>1 else mon((0,0,0),z)
    def add(*args):
        out={}
        for p in args:
            for k,c in p.items():out[k]=out.get(k,F.zero)+c
        return {k:c for k,c in out.items() if c}
    def scale(p,c):return {k:v*c for k,v in p.items() if v*c}
    def mul(p,q):
        out={}
        for (e,a,b),v in p.items():
            for (f,c,d),w in q.items():
                carry,r=divmod(e+f,g)
                key=(r,a+c,b+d)
                val=v*w*tp[(-n*(a-b)*f)%ell]*z**carry
                out[key]=out.get(key,F.zero)+val
        return {k:c for k,c in out.items() if c}
    def madd(*args):
        out={}
        for a in args:
            for ij,v in a.items():
                c=add(out.get(ij,{}),v)
                if c:out[ij]=c
                else:out.pop(ij,None)
        return out
    def mmul(a,b):
        out={}
        for (i,j),v in a.items():
            for (k,l),w in b.items():
                if j==k:out=madd(out,{(i,l):mul(v,w)})
        return out
    def mscale(a,c):return {ij:scale(v,c) for ij,v in a.items() if scale(v,c)}
    I={(i,i):one for i in range(n)}
    def mpow(a,k):
        out=I
        while k:
            if k%2:out=mmul(out,a)
            a=mmul(a,a);k//=2
        return out
    b=[mul(P,R)]+[mon((0,0,0),F.convert(v)) for v in bs]
    E=F.one
    for v in bs:E*=F.convert(v)
    um={(i,i):scale(kap,tp[i]) for i in range(n)}
    xm={(i+1,i):one for i in range(n-1)};xm[(0,n-1)]=P
    wm={(i-1,i):b[i] for i in range(1,n)};wm[(n-1,0)]=R
    checks=0
    def check(a,b):
        nonlocal checks
        difference=madd(a,mscale(b,-F.one))
        assert not difference,(ell,g,difference)
        checks+=1
    check(mmul(xm,um),mscale(mmul(um,xm),tp[-1]))
    check(mmul(wm,um),mscale(mmul(um,wm),tp[1]))
    check(mmul(xm,wm),{(i,i):b[i] for i in range(n)})
    check(mmul(wm,xm),{(i,i):b[(i+1)%n] for i in range(n)})
    check(mpow(xm,n),{(i,i):P for i in range(n)})
    check(mpow(wm,n),{(i,i):scale(R,E) for i in range(n)})
    check(mpow(xm,ell),{(i,i):mon((0,g,0)) for i in range(n)})
    check(mpow(wm,ell),{(i,i):mon((0,0,g),E**g) for i in range(n)})
    check(mpow(um,ell),mscale(I,z**n))
    check(mmul(mpow(xm,ell),mpow(wm,ell)),
          {(i,i):mon((0,g,g),E**g) for i in range(n)})
    ug=mscale(mpow(um,g),z**-1)
    for i in range(n):
        e={}
        for k in range(n):e=madd(e,mscale(mpow(ug,k),tp[(-g*i*k)%ell]/n))
        check(e,{(i,i):one})
    # Distinguish full formal model from its radical special fiber.
    assert mul(P,R)==mon((0,1,1)) and mul(R,P)==mon((0,1,1))
    assert mul(P,R)
    # Gille--Szamuely cup convention: a*P=P*sigma^{-1}(a).
    assert not add(mul(kap,P),scale(mul(P,scale(kap,tp[n%ell])),-F.one))
    checks+=1
    for center in (mon((0,g,0)),mon((0,0,g)),mon((0,1,1))):
        for a in (kap,P,R):
            assert not add(mul(center,a),scale(mul(a,center),-F.one))
            checks+=1
    return {'order':ell,'stabilizer_order':g,'matrix_size':n,
            'exact_matrix_and_center_identities':checks,
            'coefficient_field':'QQ(t)(z,b1,...,b(n-1)); t primitive ell-th root',
            'PR_nonzero':True,'edge_parameters_algebraically_independent':True,
            'cup_character_convention':'chi(sigma^{-1})=1; aP=P sigma^{-1}(a)'}

def resolution_charts(g):
    charts=[]
    for k in range(g):
        xi=(k+1,k);y=(g-k-1,g-k);s=(1,1)
        assert tuple(xi[j]+y[j] for j in range(2))==(g,g)
        assert xi[0]*s[1]-xi[1]*s[0]==1
        charts.append({'k':k,'xi_exponents':list(xi),'upsilon_exponents':list(y),
                       's_exponents':list(s),'primitive_lattice_determinant':1})
    vals=[]
    for i in range(1,g):
        assert charts[i-1]['xi_exponents'][0]==i
        assert charts[i-1]['upsilon_exponents'][0]==g-i
        order=g//gcd(g,i)
        assert (i*order)%g==0
        assert all((i*j)%g for j in range(1,order))
        vals.append({'exceptional_index':i,'valuation':[i,g-i,1],
                     'residue_character_multiple':i,'residue_order':order})
    return {'stabilizer_order':g,'toric_charts':charts,'exceptional_residues':vals}

def compute():
    models=[formal_model(ell,g) for ell in range(3,13) for g in range(1,ell+1) if ell%g==0]
    charts=[resolution_charts(g) for g in range(1,13)]
    return {'version':40,'status':'PASS','scope':'generic U-chart boundary; full formal descent, McKay model, exceptional residue valuations',
            'proof_scope':'All-order statements follow from the manuscript proof. The finite checks only verify formulas and orientations.',
            'formal_matrix_models':models,'model_count':len(models),
            'exact_identity_count':sum(x['exact_matrix_and_center_identities'] for x in models),
            'resolution_charts':charts,'g6_residue_orders':[6,3,2,3,6],
            'exact_arithmetic_only':True}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write-certificate',action='store_true')
    p.add_argument('--check',action='store_true')
    a=p.parse_args();r=compute()
    if a.check:assert r==json.loads(CERT.read_text()),'complete certificate mismatch'
    if a.write_certificate:CERT.write_text(json.dumps(r,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r,ensure_ascii=False,indent=2,sort_keys=True))

if __name__=='__main__':main()
