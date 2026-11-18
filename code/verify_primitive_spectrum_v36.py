#!/usr/bin/env python3
"""Exact finite QA for the all-weight proof in primitive_spectrum_ja_v36.tex.
Normal execution is read-only and emits the complete deterministic certificate.
No rank conclusion or general-weight theorem is inferred from these finite cases.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sympy as sp

x, y, z, w, u, v, e = sp.symbols('x y z w u v e')
VARIABLES = (x, y, z, w)
BETA = sp.Rational(4, 9)
checks = 0

def zero(expr):
    global checks
    value = sp.expand(expr)
    assert value == 0, value
    checks += 1

def rational_zero_mod(expr, relation):
    global checks
    num, den = sp.cancel(expr).as_numer_denom()
    rem = sp.rem(sp.Poly(num, v), sp.Poly(relation, v)).as_expr()
    assert sp.expand(rem) == 0, sp.factor(rem)
    assert den != 0
    checks += 1

def data(j):
    m, d = 2*j+1, 2*j+3
    q = x*z-y*y
    J = x*x*w + q**j*(x*y*z-sp.Rational(2,3)*y**3)
    D = x*x*w*w+2*w*q**j*(x*y*z-sp.Rational(2,3)*y**3)+sp.Rational(1,9)*q**(2*j)*z*z*(4*x*z-3*y*y)
    H = w+sp.Rational((-1)**j,4)*y**(m-2)*z*z
    return m,d,q,J,D,H

def invariant_checks(j):
    before = checks
    m,d,q,J,D,H=data(j)
    A=d+2
    alpha=-sp.Rational(A,m+3)
    weights=(alpha,alpha+1,alpha+2,m*alpha+d)
    def N(f): return x*sp.diff(f,y)+2*y*sp.diff(f,z)-q**j*z*sp.diff(f,w)
    def X(f): return sum(a*t*sp.diff(f,t) for a,t in zip(weights,VARIABLES))
    zero(x*x*D-J*J-BETA*q**d)
    zero(N(q)); zero(N(J)); zero(N(D))
    zero(X(q)+sp.Rational(2,m+3)*q)
    zero(X(J)+sp.Rational(d,m+3)*J)
    zero(X(D)-sp.Rational(4,m+3)*D)
    for lam in (sp.Integer(1),sp.Integer(2),sp.Rational(-3,2)):
        zero(N(q*J-lam*x))
        zero(X(q*J-lam*x)-alpha*(q*J-lam*x))
    zero(D.subs(x,0)+sp.Rational(4,3)*(-1)**j*y**d*H)
    zero(N(H).subs(x,0))
    zero(X(H)-sp.Rational(m+6,m+3)*H)
    zero(D.subs({x:0,y:0}))
    zero(H.subs(y,0)-w)
    return {"j":j,"m":m,"d":d,"checks":checks-before}

def normalization_checks(j,lam):
    before=checks
    m,d,q,J,D,H=data(j)
    eps=(-1)**j
    kappa=-sp.Rational(2,3)/lam
    rel=v*v-1-kappa*u**d*z
    xx=kappa*u**(d+2)
    yy=u*v
    ww=-sp.Rational(eps,3)*u**(d-4)*z*z*(v-2*eps)/(v-eps)**2
    subs={x:xx,y:yy,w:ww}
    qq=q.subs(subs, simultaneous=True)
    JJ=J.subs(subs, simultaneous=True)
    DD=D.subs(subs, simultaneous=True)
    rational_zero_mod(qq+u*u,rel)
    rational_zero_mod(JJ-sp.Rational(2,3)*u**d,rel)
    rational_zero_mod(qq*JJ-lam*xx,rel)
    rational_zero_mod(DD,rel)
    zero(2+eps*(3*v-v**3)+eps*(v-2*eps)*(v+eps)**2)
    rational_zero_mod(3*kappa*kappa*u**(d+4)*ww-(2+eps*(3*v-v**3)),rel)
    zero(ww.subs({u:0,v:-eps}))
    zero((v*v-1).subs(v,-eps))
    assert (2+eps*(3*v-v**3)).subs(v,eps)==4
    zero((-sp.Rational(3*eps,2)*(sp.Rational(2,3)*u**d)/(-u*u)**(j+1))-u)
    return {"j":j,"m":m,"lambda":str(lam),"checks":checks-before,
            "boundary_u_exponent":d-4,"boundary_w":0}

def saturation_check(j,lam):
    global checks
    before=checks
    m,d,q,J,D,H=data(j)
    # Elimination computes the ordinary x-saturation; the text proves that it
    # agrees with the star-ideal contraction for these N-invariant eigenvectors.
    G=sp.groebner([D,q*J-lam*x,e*x-1],e,w,z,y,x,order='lex',domain=sp.QQ)
    sat=[p.as_expr() for p in G.polys if not p.as_expr().has(e)]
    assert sat
    boundary=[sp.expand(f.subs({x:0,y:0})) for f in sat]
    BG=sp.groebner(boundary,w,z,order='lex',domain=sp.QQ)
    assert list(BG)==[w],list(BG)
    checks+=1
    canonical='\n'.join(sp.srepr(sp.Poly(f,w,z,y,x,domain=sp.QQ).as_expr()) for f in sat)
    return {"j":j,"m":m,"lambda":str(lam),"basis_size":len(sat),
            "saturation_basis_sha256":hashlib.sha256(canonical.encode()).hexdigest(),
            "boundary_groebner_basis":[str(f) for f in BG],"checks":checks-before}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-certificate',type=Path)
    args=parser.parse_args()
    inv=[invariant_checks(j) for j in range(1,7)]
    norm=[normalization_checks(j,lam) for j in range(1,7)
          for lam in (sp.Integer(1),sp.Integer(2),sp.Rational(-3,2))]
    sat=[saturation_check(j,lam) for j in (1,2,3)
         for lam in (sp.Integer(1),sp.Rational(-3,2))]
    report={"version":"v36","status":"passed","arithmetic":"QQ",
        "scope":"Finite QA of identities and saturation; general proof is in the Japanese manuscript.",
        "identity_checks":sum(r['checks'] for r in inv+norm),
        "saturation_checks":len(sat),"total_checks":checks,
        "invariant_cases":inv,"normalization_cases":norm,"saturation_cases":sat}
    txt=json.dumps(report,ensure_ascii=False,indent=2,sort_keys=True)+'\n'
    if args.write_certificate:
        args.write_certificate.write_text(txt,encoding='utf-8')
    print(txt,end='')

if __name__=='__main__':main()
