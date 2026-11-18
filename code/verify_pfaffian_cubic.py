#!/usr/bin/env python3
"""Exact QQ construction, mod-101 smoothness witness for the auxiliary cubic.
Run with python3 (SymPy available). No preexisting research files are modified.
"""
import sys
if not __debug__:
    raise RuntimeError('Do not disable certificate assertions.')
sys.dont_write_bytecode = True
import json
from pathlib import Path
import sympy as s
X=s.symbols('x y z'); x,y,z=X
G=s.Matrix([[-2,1,-3,0,-2,3],[1,2,2,-2,-3,-2],[-3,2,2,3,-2,2],[0,-2,3,1,0,1],[-2,-3,-2,0,2,0],[3,-2,2,1,0,3]])
assert G==G.T and G[:3,3:]==G[:3,3:].T
M=G.inv()
def cross(v):
    a,b,c=v
    return s.Matrix([[0,-c,b],[c,0,-a],[-b,a,0]])
Xs=[s.diag(cross([int(i==j) for j in range(3)]),cross([int(i==j) for j in range(3)])) for i in range(3)]
O=[Xs[i].T*M*Xs[j]-Xs[j].T*M*Xs[i] for i,j in [(1,2),(2,0),(0,1)]]
assert all(T==-T.T for T in O)
Om=sum((X[i]*O[i] for i in range(3)),s.zeros(6))
def pf(T):
    if T.rows==0:return s.S.One
    val=0
    for j in range(1,T.rows):
        ids=[i for i in range(T.rows) if i not in (0,j)]
        val+=(-1)**(j+1)*T[0,j]*pf(T.extract(ids,ids))
    return s.expand(val)
f=s.factor(pf(Om))
F=s.Poly(-499*f,*X)
assert F.as_expr()==22*x**3+31*x**2*y-13*x**2*z-10*x*y**2-28*x*y*z-20*x*z**2+26*y**3+10*y**2*z+11*y*z**2+9*z**3
mons=lambda d:[(a,b,d-a-b) for a in range(d+1) for b in range(d+1-a)]
mon4=mons(4); mon2=mons(2)
polys=[s.Poly(s.diff(F.as_expr(),t)*s.prod(X[i]**m[i] for i in range(3)),*X) for t in X for m in mon2]
rows=[[int(P.coeff_monomial(m))%101 for m in mon4] for P in polys]
# Independent rows selected by echelon insertion; record original row indices.
basis=[];pivs=[];sel=[]
for ri,row in enumerate(rows):
    v=row[:]
    for piv,b in zip(pivs,basis):
        t=v[piv]
        v=[(a-t*c)%101 for a,c in zip(v,b)]
    nz=next((i for i,a in enumerate(v) if a),None)
    if nz is not None:
        inv=pow(v[nz],-1,101);v=[a*inv%101 for a in v]
        at=sum(p<nz for p in pivs)
        # Re-echelon for future insertion, preserving row index list only for determinant.
        basis.insert(at,v);pivs.insert(at,nz);sel.append(ri)
assert len(sel)==15
minor=s.Matrix([rows[i] for i in sel]);det=int(minor.det())%101
assert det!=0
# The incidence coefficients: G has the required separately symmetric 2x2 blocks.
Q=s.Matrix([[sum(X[i]*G[3*a+i,3*b+j]*X[j] for i in range(3) for j in range(3)) for b in range(2)] for a in range(2)])
out={'version':1,'base_field':'QQ','prime':101,'G':[[int(t) for t in row] for row in G.tolist()],'det_G':int(G.det()),'Q':[[str(Q[i,j]) for j in range(2)] for i in range(2)],'Omega_indices':[[1,2],[2,0],[0,1]],'pfaffian':str(f),'primitive_cubic':str(F.as_expr()),'Macaulay_rows':18,'Macaulay_columns':15,'derivative_order':['x','y','z'],'multiplication_monomials':mon2,'column_monomials':mon4,'minor_rows':sel,'minor_det_mod_101':det,'claim':'The cubic is geometrically smooth over QQ because the degree-four gradient Macaulay matrix has full rank modulo 101.'}
path=Path(__file__).with_name('pfaffian_cubic_certificate.json')
if '--write' in __import__('sys').argv:path.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
else:assert json.loads(path.read_text())==json.loads(json.dumps(out))
print(json.dumps({'det_G':out['det_G'],'primitive_cubic':out['primitive_cubic'],'minor_rows':sel,'minor_det_mod_101':det,'status':'PASS'},ensure_ascii=False))
