#!/usr/bin/env python3
"""Read-only exact checks for the uniform filtered-reduction theorem.

The all-m theorem is proved by polarized antisymmetrization, finite filtered
comparison, and the displayed bidiagonal annihilator. These finite rational
checks independently reconstruct the arbitrary-weight CGG corner complex.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb
import hashlib,json,sys
sys.dont_write_bytecode=True
from vk_all_weights_model_v40 import Corner,add
from flint import fmpq_mat
HERE=Path(__file__).resolve().parent

def multiply(c,p,q):
    ans={}
    for u,a in p.items():
        for v,b in q.items():
            for w,d in c.mono(u,v).items():add(ans,w,a*b*d)
    return ans

def product_checks(c):
    height=lambda u:u[1]+2*u[2]+c.d*u[3]
    pairs=0
    for ch in combinations(c.objects,3):
        for a,b in product(c.basis(ch[1]-ch[0]),c.basis(ch[2]-ch[1])):
            ans=c.mono(a,b);lead=tuple(a[i]+b[i] for i in range(4))
            assert ans.get(lead)==1
            for z,e in ans.items():
                assert z[3]<=a[3]+b[3]
                assert height(z)<=height(a)+height(b)
                assert z==lead or height(z)<height(lead)
            pairs+=1
    triples=0
    for a,b,d in product(c.basis(1),c.basis(c.m-1),c.basis(1)):
        assert multiply(c,c.mono(a,b),{d:Q(1)})==multiply(c,{a:Q(1)},c.mono(b,d))
        triples+=1
    w=(0,0,0,1)
    primitive_outputs=[u for u in c.basis(c.m+1) if u[3]]
    left=fmpq_mat([[str(c.mono(v,w).get(u,0)) for v in c.basis(1)] for u in primitive_outputs])
    assert left.rank()==3
    return {'relevant_input_pairs':pairs,'associativity_triples':triples,
            'w_filtration_preserved':True,'auxiliary_height_strict_lower_corrections':True,
            'primitive_left_product_rank':3}

def extremal(j,r):
    m=2*j+r;d=m+r+1
    assert m>=3
    ell=[Q(1)]
    for b in range(j):ell.append(-Q(2*(b+r+1),2*j-1-2*b)*ell[-1])
    # Columns of N on the X-weight d subspace, in the displayed monomial bases.
    M=fmpq_mat(j+1,j)
    for b in range(j):
        M[b,b]=2*(b+r+1)
        M[b+1,b]=2*j-1-2*b
    cov=fmpq_mat([[str(v) for v in ell]])
    assert cov*M==fmpq_mat(1,j)
    assert M.rank()==j
    P=[Q((-1)**(j-b)*comb(j,b)) for b in range(j+1)]
    obstruction=sum(x*y for x,y in zip(ell,P))
    assert obstruction and (obstruction>0)==(j%2==0)
    c=Corner(j,r)
    domain=[u for u in c.basis(m) if not u[3] and u[1]+2*u[2]==d]
    expected=[(b,2*j-1-2*b,b+r+1,0) for b in range(j)]
    assert set(domain)==set(expected)
    for b,u in enumerate(expected):
        image=c.N({u:Q(1)})
        exp={}
        add(exp,(b,2*j-2*b,b+r,0),Q(2*(b+r+1)))
        add(exp,(b+1,2*j-2*b-2,b+r+1,0),Q(2*j-1-2*b))
        assert image==exp
    return {'j':j,'r':r,'m':m,'domain_dimension':j,'N_rank':j,
            'annihilator_pairing_with_qj_zr':str(obstruction)}

def projective_poisson_stabilizer():
    from sympy import symbols,Poly,expand,diff
    Y,Z=symbols('Y Z')
    v=symbols('a0 a1 a2 b0 b1 b2 c0 c1 c2')
    a0,a1,a2,b0,b1,b2,c0,c1,c2=v
    fy=b0+(b1-a0)*Y+b2*Z-a1*Y**2-a2*Y*Z
    fz=c0+c1*Y+(c2-a0)*Z-a1*Y*Z-a2*Z**2
    g=Z-Y**2
    obstruction=Poly(expand(fy*diff(g,Y)+fz*diff(g,Z)-g*(diff(fy,Y)+diff(fz,Z))),Y,Z)
    terms=obstruction.terms()
    M=fmpq_mat([[int(diff(c,x)) for x in v] for mon,c in terms])
    E=fmpq_mat([[1],[0],[0],[0],[1],[0],[0],[0],[1]])
    N=fmpq_mat([[0],[0],[0],[1],[0],[0],[0],[2],[0]])
    assert M.rank()==7
    assert M*E==fmpq_mat(M.nrows(),1) and M*N==fmpq_mat(M.nrows(),1)
    return {'variables':[str(x) for x in v],'monomials':[list(mon) for mon,c in terms],
            'coefficient_matrix':[[str(M[i,j]) for j in range(M.ncols())] for i in range(M.nrows())],
            'rank':7,'kernel_basis':['scalar Euler matrix','N=x*d_y+2*y*d_z'],
            'projective_stabilizer_dimension':1}

def compute():
    cases=[]
    for m in range(3,8):
        n=lambda d:comb(d+2,2)
        for j in range(m//2+1):
            r=m-2*j;c=Corner(j,r)
            q=c.ranks('Q');k=c.ranks('K')
            assert q['dimensions']==[2*n(m)+3*n(m+1),6*n(m-1)+18*n(m),27*n(m-1)]
            assert q['cohomology']==[0,0,4*m*m-6*m-7]
            assert k['dimensions']==[2*n(m)+3*n(m+1)+11,6*n(m+1)+18,0]
            assert k['cohomology']==[0,(m*m+9*m+28)//2,0]
            cases.append({'j':j,'r':r,'m':m,'positive_quotient':q,'primitive_relative':k,'product_checks':product_checks(c)})
    comm=[]
    for m in range(3,8):
        c=Corner(0,m,s=0);v=c.ranks('Q')
        assert v['cohomology']==[0,0,4*m*m-6*m-7]
        comm.append(v)
    weights=[extremal(j,r) for j in range(9) for r in range(9) if 2*j+r>=3]
    src=HERE/'vk_all_weights_model_v40.py'
    return {'version':40,'status':'PASS','arithmetic':'QQ; Fraction and python-flint',
            'scope':'All-m theorem is proved in text; exact finite checks cover all resonances 3<=m<=7, including endpoints, and explicit obstruction recurrence.',
            'model_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
            'resonant_cases':cases,'commutative_positive_complex_cases':comm,
            'extremal_annihilator_cases':weights,
            'projective_poisson_stabilizer':projective_poisson_stabilizer(),
            'framed_relative_dimension_formula':'(m^2+9m+28)/2',
            'ordinary_hull_splitting_all_m_claimed':True,
            'ordinary_hull_scope':'R_Bjr = R_Nm[[k_m]]; R_Nm itself is not determined for general m.',
            'checks':{'all_relevant_products_filtered':True,'all_adjacent_triples_associative':True,
                      'quotient_H1_H2_zero':True,'relative_H1_zero_H2_dimension':True,
                      'extremal_recurrence_left_annihilator_and_nonzero_pairing':True,
                      'chart_projective_Poisson_stabilizer_rank7':True}}

if __name__=='__main__':
    actual=compute()
    if '--dump' not in sys.argv:
        expected=json.loads((HERE/'vk_all_weights_filtered_v40_certificate.json').read_text())
        assert actual==expected,'frozen certificate mismatch'
    print(json.dumps(actual,indent=2,sort_keys=True))
