#!/usr/bin/env python3
"""Independent exact checks of the normal charts used in the v37 spectrum proof.

The proof in the manuscript is uniform in j,r. This certificate checks twenty-two
explicit admissible pairs over QQ; it is supporting arithmetic, not a replacement
for that proof. The default command reads its frozen certificate and never edits it.
"""
from pathlib import Path
import json
import sys
import sympy as sp

x,y,z,w=sp.symbols('x y z w')
variables=(x,y,z,w)

def require(condition,label):
    if not condition:
        raise AssertionError(label)

def zero(expression,label):
    require(sp.cancel(sp.expand(expression))==0,label)

def derivation(components,expression):
    return sum(c*sp.diff(expression,v) for c,v in zip(components,variables))

def one_case(j,r):
    m=2*j+r
    require(m>=3 and r>0,'admissible parameters')
    A=m+r+3
    d=m+r+1
    alpha=-sp.Rational(A,m+3)
    weights=(alpha,alpha+1,alpha+2,m*alpha+d)
    integer_weights=(-A,-r,2*j+3,m+3*r+3)
    require(tuple((m+3)*a for a in weights)==integer_weights,'CY integer weights')
    q=x*z-y*y
    nc=(0,x,2*y,-q**j*z**r)
    xc=tuple(a*v for a,v in zip(weights,variables))
    N=lambda f:derivation(nc,f)
    X=lambda f:derivation(xc,f)
    for v in variables:
        zero(N(X(v))-X(N(v))-N(v),'Lie relation on '+str(v))
    J=x**(r+1)*w+q**j*sum(sp.binomial(r,k)*q**(r-k)*y**(2*k+1)/sp.Integer(2*k+1) for k in range(r+1))
    zero(N(q),'Nq=0')
    zero(N(J),'NJ=0')
    zero(X(q)-2*(alpha+1)*q,'q eigenweight')
    zero(X(J)-d*(alpha+1)*J,'J eigenweight')
    tx=y/x
    zero(N(tx)-1,'x-chart Nt=1')
    zero(X(tx)-tx,'x-chart Xt=t')
    zero(N(x),'x-chart normal eigenunit')
    require(weights[0]!=0,'x-chart nonzero weight')
    # The coordinate inverse on the x-chart is polynomial in t over K.
    tau,qq,jj=sp.symbols('tau qq jj')
    yy=x*tau
    zz=(qq+yy**2)/x
    ww=(jj-qq**j*sum(sp.binomial(r,k)*qq**(r-k)*yy**(2*k+1)/sp.Integer(2*k+1) for k in range(r+1)))/x**(r+1)
    substitutions={y:yy,z:zz,w:ww}
    zero(q.subs(substitutions,simultaneous=True)-qq,'x-chart inverse q')
    zero(J.subs(substitutions,simultaneous=True)-jj,'x-chart inverse J')
    nc_y=tuple(sp.sympify(c).subs(x,0) for c in nc)
    N_y=lambda f:derivation(nc_y,f)
    H=w+sp.Rational((-1)**j,2*(r+1))*y**(2*j-1)*z**(r+1)
    ty=z/(2*y)
    zero(N_y(H),'y-chart NH=0')
    zero(X(H)-weights[3]*H,'y-chart H eigenweight')
    zero(N_y(ty)-1,'y-chart Nt=1')
    zero(X(ty)-ty,'y-chart Xt=t')
    zero(N_y(y),'y-chart normal eigenunit')
    require(weights[1]!=0,'y-chart nonzero weight')
    hh=sp.symbols('hh')
    yz=2*y*tau
    yw=hh-sp.Rational((-1)**j,2*(r+1))*y**(2*j-1)*yz**(r+1)
    zero(H.subs({z:yz,w:yw},simultaneous=True)-hh,'y-chart inverse H')
    # These three minors force exactly the asserted rank-zero support.
    minors={(a,b):sp.expand(nc[a]*xc[b]-nc[b]*xc[a]) for a in range(4) for b in range(a+1,4)}
    zero(minors[0,1]+alpha*x*x,'xy minor forces x=0')
    zero(minors[1,2].subs(x,0)+2*(alpha+1)*y*y,'yz minor then forces y=0')
    for value in minors.values():
        substitution={x:0,y:0} if j>=1 else {x:0,y:0,z:0}
        zero(value.subs(substitution),'all minors vanish on F')
    z_chart=None
    if j==0:
        nc_z=(0,0,0,-z**r)
        N_z=lambda f:derivation(nc_z,f)
        tz=-w/z**r
        zero(N_z(tz)-1,'z-chart Nt=1')
        zero(X(tz)-tz,'z-chart Xt=t')
        zero(minors[2,3].subs({x:0,y:0})-weights[2]*z**(r+1),'zw minor then forces z=0')
        require(weights[2]!=0,'z-chart nonzero weight')
        zero(tz.subs(w,-tau*z**r)-tau,'z-chart inverse t')
        z_chart={'normal_weight':str(weights[2]),'Nt':'1','Xt':'t','K':'QQ[z,z^-1]'}
    else:
        for c in nc:
            zero(sp.sympify(c).subs({x:0,y:0}),'N=0 on rank-zero plane')
    return {'j':j,'r':r,'m':m,'alpha':str(alpha),'integer_weights':list(integer_weights),'q_weight':str(2*(alpha+1)),'J_weight':str(d*(alpha+1)),'H_weight':str(weights[3]),'x_chart':{'normal_weight':str(weights[0]),'Nt':'1','Xt':'t','Nq':'0','NJ':'0','coordinate_inverse':'PASS'},'y_chart':{'normal_weight':str(weights[1]),'Nt':'1','Xt':'t','NH':'0','H_eigenweight':'PASS','coordinate_inverse':'PASS'},'z_chart':z_chart,'rank_zero_support':'V(x,y)' if j>=1 else 'V(x,y,z)','minor_checks':'PASS','Lie_relation':'[N,X]=N'}

def certificate():
    pairs=[(j,r) for j in range(4) for r in range(1,7) if 2*j+r>=3]
    return {'version':37,'status':'PASS','arithmetic':'QQ','scope':'Independent symbolic checks at 22 admissible parameter pairs; the manuscript supplies the uniform proof.','cases':[one_case(j,r) for j,r in pairs]}

if __name__=='__main__':
    actual=certificate()
    if sys.argv[1:]==['--emit-candidate']:
        print(json.dumps(actual,indent=2))
    else:
        require(not sys.argv[1:],'no unrecognized arguments')
        expected=json.loads(Path(__file__).with_name('normal_charts_v37_certificate.json').read_text())
        require(actual==expected,'frozen normal-chart certificate')
        print(json.dumps(actual,indent=2))
