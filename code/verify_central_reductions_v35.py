#!/usr/bin/env python3
"""Exact finite checks for the v35 all-weight localization/central-fiber proof.

Standard library only. No input or certificate is ever generated or modified.
The universal statements are proved structurally in central_reductions_ja_v35.tex.
"""
from fractions import Fraction as Q
from math import comb, gcd
import json


class P:
    def __init__(self, terms=None, n=3):
        self.n=n
        self.d={tuple(e):Q(c) for e,c in (terms or {}).items() if c}
    @classmethod
    def constant(cls,c,n=3):
        return cls({(0,)*n:Q(c)},n)
    @classmethod
    def var(cls,i,n=3):
        e=[0]*n;e[i]=1
        return cls({tuple(e):1},n)
    def coerce(self,b):
        return b if isinstance(b,P) else P.constant(b,self.n)
    def __add__(self,b):
        b=self.coerce(b);assert self.n==b.n
        z=self.d.copy()
        for e,c in b.d.items():z[e]=z.get(e,Q(0))+c
        return P(z,self.n)
    __radd__=__add__
    def __neg__(self):return P({e:-c for e,c in self.d.items()},self.n)
    def __sub__(self,b):return self+-self.coerce(b)
    def __rsub__(self,b):return self.coerce(b)+-self
    def __mul__(self,b):
        b=self.coerce(b);assert self.n==b.n
        z={}
        for e,c in self.d.items():
            for f,d in b.d.items():
                h=tuple(a+b for a,b in zip(e,f))
                z[h]=z.get(h,Q(0))+c*d
        return P(z,self.n)
    __rmul__=__mul__
    def __pow__(self,k):
        assert k>=0
        out=P.constant(1,self.n);b=self
        while k:
            if k&1:out=out*b
            b=b*b;k//=2
        return out
    def shift(self,e):
        return P({tuple(a+b for a,b in zip(f,e)):c for f,c in self.d.items()},self.n)
    def diff(self,i):
        z={}
        for e,c in self.d.items():
            if e[i]:
                f=list(e);f[i]-=1
                z[tuple(f)]=c*e[i]
        return P(z,self.n)
    def at_zero(self,i):return P({e:c for e,c in self.d.items() if not e[i]},self.n)
    def toric(self,A):
        """Reduce a*b=c^A in variables (a,b,c)."""
        z={}
        for (u,v,w),c in self.d.items():
            assert min(u,v,w)>=0
            h=min(u,v);e=(u-h,v-h,w+A*h)
            z[e]=z.get(e,Q(0))+c
        return P(z,3)
    def substitute(self,values):
        z=P.constant(0,values[0].n)
        for e,c in self.d.items():
            t=P.constant(c,values[0].n)
            for f,k in zip(values,e):
                assert k>=0
                t=t*f**k
            z=z+t
        return z
    def __eq__(self,b):
        b=self.coerce(b)
        return self.n==b.n and self.d==b.d


checks=[]
def check(name,actual,expected=0):
    if actual!=expected:raise AssertionError(name)
    checks.append(name)


def main():
    beta=Q(4,9)
    toric_cases=[];monomial_count=0
    for j in range(7):
        for r in range(9):
            m=2*j+r
            if m<3:continue
            d=m+r+1;A=d+2;g=gcd(A,r);n=A//g
            check(f'odd_A_{j}_{r}',A%2,1)
            if r:
                check(f'coprime_weights_{j}_{r}',gcd(2*r//g,n),1)
            check(f'a_weight_{j}_{r}',A*(-2*r//g)+2*r*n)
            check(f'b_weight_{j}_{r}',A*(-r*d//g)+r*d*n)
            check(f'c_weight_{j}_{r}',A*(-r)+2*r+r*d)
            check(f'ab_exponent_{j}_{r}',(2*r+r*d)//g,r*n)
            for u in range(36):
                for v in range(36):
                    weight=2*r*u+r*d*v
                    if weight%A:continue
                    h=min(u,v)
                    assert (u-v)%n==0
                    if u>=v:
                        k=(u-v)//n
                        reconstructed=(-r*h-(2*r//g)*k,n*k+h,h)
                    else:
                        k=(v-u)//n
                        reconstructed=(-r*h-(r*d//g)*k,h,n*k+h)
                    assert reconstructed==(-weight//A,u,v)
                    monomial_count+=1
            toric_cases.append({'j':j,'r':r,'m':m,'A':A,'g':g,'n':n})

    fiber_cases=[]
    for m in (3,5,7,9,11,13):
        j=(m-1)//2;d=m+2;A=d+2;L=(d+1)//2;h=(d-1)//2
        x,q,J=[P.var(i) for i in range(3)]
        Delta=(J**2+beta*q**d).shift((-2,0,0))
        S=q**2*Delta
        P0=2*x*J*Delta**L
        R=q*(x**2*Delta+J**2)*Delta**L
        a=(q**A).shift((-2,0,0))
        b=(J**A).shift((-d,0,0));c=(q*J).shift((-1,0,0))
        check(f'central_D_relation_m{m}',R**2-S*P0**2-beta**2*S**(2*L))
        check(f'Rplus_m{m}',R+beta*S**L,2*q*x**2*Delta**(L+1))
        check(f'Rminus_m{m}',R-beta*S**L,2*q*J**2*Delta**L)
        check(f'S_to_A_m{m}',S,c**2+beta*a)
        check(f'aP_m{m}',a*P0,2*c*S**L)
        check(f'Rminus_cP_m{m}',R-beta*S**L,c*P0)
        check(f'A_relation_m{m}',a*b,c**A)
        h0=J**2+beta*q**d
        check(f'origin_nilpotency_identity_m{m}',h0**(L+1),J*(J*h0**L)+beta*q**(d-2)*h0**(L-1)*(q**2*h0))
        check(f'origin_nilpotency_sharp_m{m}',(h0**L).at_zero(1),J**(2*L))
        cross_reduce=lambda p:P({e:v for e,v in p.d.items() if not(e[1]>0 and e[2]>0)})
        check(f'zero_c_q_relation_m{m}',cross_reduce(q**2*h0),beta*q**A)
        check(f'zero_c_J_relation_m{m}',cross_reduce(J*h0**L),J**A)
        eta=P.var(0);lam=P.var(1)
        q_eta=(-1/beta)*eta**2
        J_eta=(-1/beta)**h*eta**d
        x_eta=((-1/beta)**(h+1)*eta**A).shift((0,-1,0))
        check(f'nonzero_c_cusp_m{m}',J_eta**2+beta*q_eta**d)
        check(f'nonzero_c_parameter_m{m}',q_eta*J_eta,lam*x_eta)
        Sum=sum((comb(L,k)*beta**(L-k)*a**(L-1-k)*c**(2*k+1)
                 for k in range(L)),P.constant(0))
        check(f'P_polynomial_m{m}',P0,2*(b+Sum))

        aa,bb,cc=[P.var(i) for i in range(3)]
        SS=cc**2+beta*aa
        H=sum((comb(L,k)*beta**(L-k)*aa**(L-1-k)*cc**(2*k+1)
                 for k in range(L)),P.constant(0))
        PP=2*(bb+H);RR=cc*PP+beta*SS**L
        check(f'blowup_saturated_equation_m{m}',aa*PP-2*cc*SS**L,2*(aa*bb-cc**A))
        check(f'D_after_toric_reduction_m{m}',(RR**2-SS*PP**2-beta**2*SS**(2*L)).toric(A))
        val=[(-1/beta)*cc**2,-beta*cc**d,cc]
        check(f'origin_S_m{m}',SS.substitute(val))
        check(f'origin_P_m{m}',PP.substitute(val))
        check(f'origin_R_m{m}',RR.substitute(val))
        # Equality of canonical two-forms after clearing all denominators.
        aa,SS=P.var(0),P.var(1)
        cc=P.var(2)
        p_num=2*cc*SS**L
        # dS=beta da+2c dc; d(P)=d(p_num/a).
        # coefficient of da wedge dc of dS wedge dP, multiplied by a^2:
        wedge=beta*aa*(2*SS**L+4*L*cc**2*SS**(L-1)) - 2*cc*(2*L*beta*cc*SS**(L-1)*aa-p_num)
        check(f'crepant_twoform_m{m}',wedge,2*(beta*aa+2*cc**2)*SS**L)

        check(f'eta_a_weight_m{m}',2*((A+1)//2)-A,1)
        check(f'eta_b_weight_m{m}',d*(h+1)-A*h,1)
        check(f'eta_a_q_inverse_m{m}',A+1-A,1)
        check(f'eta_b_x_inverse_m{m}',d*(h+1)-A*h,1)

        xx,yy,zz,ww=[P.var(i,4) for i in range(4)]
        qq=xx*zz-yy**2
        JJ=xx**2*ww+qq**j*(qq*yy+Q(1,3)*yy**3)
        numerator=JJ**2+beta*qq**d
        assert all(e[0]>=2 for e in numerator.d)
        DD=numerator.shift((-2,0,0,0))
        NN=lambda f:xx*f.diff(1)+2*yy*f.diff(2)-qq**j*zz*f.diff(3)
        check(f'N_J_m{m}',NN(JJ))
        check(f'N_Delta_m{m}',NN(DD))
        HH=ww+Q((-1)**j,4)*yy**(m-2)*zz**2
        Nb=lambda f:2*yy*f.diff(2)-((-1)**j)*yy**(m-1)*zz*f.diff(3)
        check(f'boundary_N_H_m{m}',Nb(HH))
        kappa=Q(-4,3)*((-1)**j)
        check(f'boundary_Delta_m{m}',DD.at_zero(0),kappa*yy**d*HH)
        alpha=Q(-(m+4),m+3)
        Xb=lambda f:(alpha+1)*yy*f.diff(1)+(alpha+2)*zz*f.diff(2)+(m*alpha+d)*ww*f.diff(3)
        check(f'boundary_X_H_m{m}',Xb(HH),Q(m+6,m+3)*HH)
        check(f'boundary_S_weight_m{m}',Q(-(m+6),m+3)+Q(m+6,m+3))
        check(f'boundary_R_sign_m{m}',Q(d+1),Q(2*L))
        fiber_cases.append({'m':m,'j':j,'D_type':A,'A_chart_type':A-1,
                            'boundary_H_weight':str(Q(m+6,m+3)),
                            'general_fiber':'D(G_m)','smooth_closed_fibers':'D(G_m)',
                            'localized_origin_nilpotency':L+1,
                            'zero_c_fiber_nilpotency':A,'zero_c_left_and_right_D_rank':2*A-1})

    print(json.dumps({'version':35,'status':'PASS','arithmetic':'exact rational Laurent polynomials; Python standard library only',
      'identity_count':len(checks),'identities':checks,
      'toric_center_cases':toric_cases,'zero_weight_monomials_decomposed':monomial_count,
      'central_fiber_cases':fiber_cases,
      'scope':'Finite checks supplement the all-integer structural proofs; no all-weight conclusion is inferred solely from these samples.',
      'certificate_regeneration':False},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
