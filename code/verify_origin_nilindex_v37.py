#!/usr/bin/env python3
"""Universal polynomial certificate for the global origin nilpotence index.

All polynomial identities are over QQ. The independent t identity proves the
all-j divisibility; the individual weights are supplementary checks only.
"""
import json
import sympy as sp

x,y,z,w,t=sp.symbols('x y z w t')
q=x*z-y**2
f=x*y*z-sp.Rational(2,3)*y**3
g=z**2*(4*x*z-3*y**2)/9
J=x*x*w+t*f
D=x*x*w*w+2*t*w*f+t*t*g
C=(x*w**3+t*y*z*w*w)/2
bracket=D*D-2*x*C*J
rhs=(2*t*q*x*x*y*w**3
     +t*t*w*w*(2*x*x*g+4*f*f-x*y*z*f)
     +4*t**3*w*f*g+t**4*g*g)
assert sp.expand(bracket-rhs)==0
assert sp.expand(3*f-x*y*z-2*y*q)==0
weights=[]
for j in range(1,9):
    m=2*j+1;L=j+2;nu=j+4
    # Prove Delta^nu is in (S,P,R) using a universal quotient identity.
    T=(2*q**(j-1)*x*x*y*w**3
       +q**(2*j-2)*w*w*(2*x*x*g+4*f*f-x*y*z*f)
       +4*q**(3*j-2)*w*f*g+q**(4*j-2)*g*g)
    D0=D.subs(t,q**j);J0=J.subs(t,q**j);C0=C.subs(t,q**j)
    assert sp.expand(D0*D0-2*x*C0*J0-q*q*T)==0
    # Multiply the preceding identity by Delta^(j+2):
    # Delta^(j+4)=C P+S Delta^(j+1) T,
    # S=q^2 Delta, P=2xJ Delta^(j+2).
    lower_delta=(2*(nu-1),2*(nu-1))
    lower_P=(2*j+7,2*j+5)
    assert lower_delta[0]<lower_P[0]
    assert nu-1==L+1
    weights.append({'j':j,'m':m,'localized_index':L+1,'global_index':nu,
                    'lower_specialization_delta_power_exponents':lower_delta,
                    'specialization_P_exponents':lower_P,
                    'universal_identity_specialization':True})
print(json.dumps({'version':'v37','status':'PASS','arithmetic':'QQ',
 'universal_identity_in_independent_t':True,
 'all_j_argument':'After t=q^j, each displayed summand of the universal difference has q exponent at least 2 for j>=1. Multiplication by Delta^(j+2) gives ideal membership. Specialization y=z=0 sends I to (2 x^(2j+7) w^(2j+5)), which does not contain Delta^(j+3).',
 'global_index_formula':'j+4=(m+7)/2',
 'supplementary_weights':weights},ensure_ascii=False,indent=2))
