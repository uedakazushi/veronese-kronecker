#!/usr/bin/env python3
"""Symbolic identity placing auxiliary Pfaffian cubics in a Hesse family."""
import sys
if not __debug__:
    raise RuntimeError('Do not disable certificate assertions.')
sys.dont_write_bytecode = True
import json
from pathlib import Path
import sympy as s
x,y,z,t=s.symbols('x y z t')
A=s.Matrix([[0,1,0],[1,0,0],[0,0,1]])
C=s.Matrix([[1,0,0],[0,0,2],[0,2,0]])
D=s.Matrix([[0,0,1],[0,t,0],[1,0,0]])
G=A.row_join(C).col_join(C.row_join(D));M=G.inv()
def cr(v):
 a,b,c=v
 return s.Matrix([[0,-c,b],[c,0,-a],[-b,a,0]])
J=[s.diag(cr([int(i==j) for j in range(3)]),cr([int(i==j) for j in range(3)])) for i in range(3)]
O=[J[i].T*M*J[j]-J[j].T*M*J[i] for i,j in [(1,2),(2,0),(0,1)]]
Omega=x*O[0]+y*O[1]+z*O[2]
def pf(T):
 if T.rows==0:return s.S.One
 ans=0
 for j in range(1,T.rows):
  ids=[i for i in range(T.rows) if i not in (0,j)]
  ans+=(-1)**(j+1)*T[0,j]*pf(T.extract(ids,ids))
 return s.factor(ans)
F=2*t*x**3+y**3+t*z**3+(t-8)*x*y*z
assert s.factor(G.det())==t-4
assert s.factor(pf(Omega)+F/(t-4))==0
assert s.factor((t-8)**3+54*t**2)==(t-2)*(t+16)**2
# Elementary smoothness check at t=1: derivative equations and their product.
assert F.subs(t,1)==2*x**3+y**3+z**3-7*x*y*z
assert (-7)**3+27*2==-289
h=s.symbols('h')
Aw=s.Rational(3,4)*h*(8-h**3)
Bw=2-5*h**3-h**6/s.Integer(4)
Jw=s.factor(1728*4*Aw**3/(4*Aw**3+27*Bw**2))
assert s.factor(Jw-27*h**3*(8-h**3)**3/(1+h**3)**3)==0
u=(t-8)**3/(54*t**2)
Jt=s.factor(27*u*(8-u)**3/(1+u)**3)
assert s.factor(Jt+((t-8)**3*((t-8)**3-432*t**2)**3)/(2*t**2*(t-2)**3*(t+16)**6))==0
assert s.limit(Jt/t,t,s.oo)==-s.Rational(1,2)
out={'status':'PASS','j_invariant':str(Jt),'j_at_infinity_leading_coefficient':'-1/2','coefficient_field':'QQ(t)','A':str(A),'C':str(C),'D':str(D),'det_G':'t - 4','Pfaffian':str(-F/(t-4)),'Hesse_cubic':str(F),'Hesse_nondegeneracy_factor':'(t - 2)*(t + 16)**2','excluded_parameter_values':[0,2,4,-16],'smooth_witness_parameter':1,'smooth_witness_product_check':-289,'proof':'For a*x^3+b*y^3+c*z^3+d*x*y*z with abc != 0, any singular projective point has xyz != 0; multiplying its derivative equations forces d^3+27abc=0.'}
path=Path(__file__).with_name('hesse_family_certificate.json')
if '--write' in __import__('sys').argv:path.write_text(json.dumps(out,indent=2)+'\n')
else:assert json.loads(path.read_text())==out
print(json.dumps(out))
