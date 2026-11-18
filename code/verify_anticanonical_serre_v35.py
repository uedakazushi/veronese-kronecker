#!/usr/bin/env python3
"""Independent finite checks of the positive-shift bimodule calculation.

Exact arithmetic over F_1000003.  The x-arrow equations are solved by the
invertible conjugation sigma^i=(1+N)^(-i alpha); all remaining generator-arrow
equations in the finite Beilinson window are then imposed directly.  Modular
ranks give upper bounds for rational kernel dimensions.  The manuscript's
explicit central monomials provide matching characteristic-zero lower bounds.
This is a finite consistency check, not the proof of the all-weight theorem.
No input or certificate is written by the verifier.
"""
from functools import lru_cache
from math import comb
import json

PRIME = 1000003


def clean(poly):
    return {e: c % PRIME for e, c in poly.items() if c % PRIME}


def add_scaled(out, poly, scalar):
    for e, c in poly.items():
        out[e] = (out.get(e, 0) + scalar * c) % PRIME


def mul_monomial(poly, exponent, scalar=1):
    return {tuple(a+b for a, b in zip(e, exponent)): c*scalar % PRIME
            for e, c in poly.items() if c*scalar % PRIME}


def weighted_basis(m, degree):
    return [(degree-m*w-z-y, y, z, w)
            for w in range(degree//m+1)
            for z in range(degree-m*w+1)
            for y in range(degree-m*w-z+1)]


class CGG:
    def __init__(self, m, r):
        self.m=m; self.r=r; self.j=(m-r)//2; self.d=m+r+1
        self.alpha=(-(m+r+3)*pow(m+3,-1,PRIME)) % PRIME
        self.P={(h,2*(self.j-h),h+r,0): ((-1)**(self.j-h)*comb(self.j,h)) % PRIME
                for h in range(self.j+1)}
        self.gens=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
        self.weights=[1,1,1,m]

    def Xweight(self,e):
        x,y,z,w=e
        return (self.alpha*(x+y+z+self.m*w)+y+2*z+self.d*w)%PRIME

    def N(self,poly):
        out={}
        for (x,y,z,w),c in poly.items():
            if y:add_scaled(out,{(x+1,y-1,z,w):y},c)
            if z:add_scaled(out,{(x,y+1,z-1,w):2*z},c)
            if w:add_scaled(out,mul_monomial(self.P,(x,y,z,w-1)),-w*c)
        return clean(out)

    @lru_cache(None)
    def powers(self,e):
        rows=[];p={e:1}
        while p:
            rows.append(p);p=self.N(p)
        return tuple(rows)

    @lru_cache(None)
    def binomial(self,value,n):
        out=1
        for k in range(n):out=out*(value-k)*pow(k+1,-1,PRIME)%PRIME
        return out

    @lru_cache(None)
    def sigma(self,e,i):
        out={};value=-i*self.alpha%PRIME
        for n,p in enumerate(self.powers(e)):
            add_scaled(out,p,self.binomial(value,n))
        return clean(out)

    @lru_cache(None)
    def right_generator(self,e,k):
        out={};a=self.gens[k];value=self.Xweight(a)
        for n,p in enumerate(self.powers(e)):
            add_scaled(out,mul_monomial(p,a),self.binomial(value,n))
        return clean(out)

    @lru_cache(None)
    def left_generator(self,k,e):
        out={};a=self.gens[k];value=self.Xweight(e)
        for n,p in enumerate(self.powers(a)):
            add_scaled(out,mul_monomial(p,e),self.binomial(value,n))
        return clean(out)

    def relation(self,e,i,k):
        out={}
        for f,c in self.sigma(e,i+self.weights[k]).items():
            add_scaled(out,self.right_generator(f,k),c)
        for f,c in self.sigma(e,i).items():
            add_scaled(out,self.left_generator(k,f),-c)
        return clean(out)


def sparse_column_rank(columns):
    pivots={}
    for column in columns:
        v=column.copy()
        while v:
            pivot=min(v)
            if pivot not in pivots:
                inv=pow(v[pivot],-1,PRIME)
                pivots[pivot]={k:c*inv%PRIME for k,c in v.items()}
                break
            factor=v[pivot]
            for row,c in pivots[pivot].items():
                value=(v.get(row,0)-factor*c)%PRIME
                if value:v[row]=value
                else:v.pop(row,None)
    return len(pivots)


def expected_kernel(m,r,n):
    if r>=2:return 0
    ell=m+3
    if r==0:
        return sum(1 for b in range(n*ell//(m+1)+1)
                   if (n*ell-(m+1)*b)%2==0)
    # D-type ring is free of rank two over C[S,P], with basis 1,R.
    return sum(1 for c in (0,1) for b in range(n//(m+2)+1)
               if n-c*ell-b*(m+2)>=0 and (n-c*ell-b*(m+2))%2==0)


def check_case(m,r,n):
    alg=CGG(m,r);ell=m+3;degree=n*ell;basis=weighted_basis(m,degree)
    blocks=[(i,k) for k in (1,2,3) for i in range(ell-alg.weights[k])]
    coordinates={}
    offset=0
    for block in blocks:
        _,k=block
        coordinates[block]={e:offset+h for h,e in enumerate(weighted_basis(m,degree+alg.weights[k]))}
        offset+=len(coordinates[block])
    columns=[];x_equations=0
    for e in basis:
        col={}
        for i in range(ell-1):
            if alg.relation(e,i,0):raise AssertionError('x conjugation relation failed')
            x_equations+=1
        for i,k in blocks:
            rel=alg.relation(e,i,k)
            coord=coordinates[(i,k)]
            col.update({coord[f]:c for f,c in rel.items()})
        columns.append(col)
    rank=sparse_column_rank(columns)
    kernel=len(basis)-rank
    target=expected_kernel(m,r,n)
    if kernel!=target:raise AssertionError((m,r,n,kernel,target))
    return {'m':m,'r':r,'j':alg.j,'anticanonical_degree':n,'coordinate_degree':degree,
            'remaining_unknowns':len(basis),'generator_arrow_blocks':len(blocks),
            'scalar_equations':offset,'verified_x_arrow_relations':x_equations,
            'rank_mod_prime':rank,'kernel_dimension_mod_prime':kernel,
            'explicit_central_lower_bound':target,'rational_kernel_dimension_certified':kernel}


def monomial_semigroup_checks():
    count=0
    for m in range(4,22,2):
        ell=m+3
        for a in range(3*ell+1):
            for b in range(3*ell+1):
                if (2*a+(m+1)*b)%ell:continue
                low=min(a,b);aa=(a-low)//ell;bb=(b-low)//ell
                if (a-low)%ell or (b-low)%ell:raise AssertionError('Veronese congruence')
                if aa*ell+low!=a or bb*ell+low!=b:raise AssertionError('Semigroup generation')
                if aa and bb:raise AssertionError('Noncanonical normal monomial')
                count+=1
    return count


def main():
    cases=[(3,3,1),(3,1,1),(3,3,2),(3,1,2),(4,0,1),(4,0,2),(4,2,1),(4,4,1)]
    rows=[check_case(*case) for case in cases]
    output={'status':'PASS','version':35,'arithmetic':'Exact finite-field arithmetic with rational kernel-dimension upper bounds and explicit characteristic-zero lower bounds',
            'prime':PRIME,'bimodule_cases':rows,'A_type_semigroup_monomials':monomial_semigroup_checks(),
            'scope':'Finite Beilinson-bimodule checks; universal equalities and derived invariance are proved structurally in the manuscript.',
            'input_files_written':False}
    print(json.dumps(output,ensure_ascii=False,indent=2))


if __name__=='__main__':main()
