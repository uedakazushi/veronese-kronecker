#!/usr/bin/env python3
"""Exact checks for the root-of-unity center and normalized central fibers.

Normal use is read-only: --check compares the full freshly computed result with
the frozen certificate.  --write-certificate is an explicit development action.
The all-order proofs are in endpoint_root_unity_ja_v38.tex, not inferred from
the finite set of orders tested here.
"""
from pathlib import Path
from collections import deque
import argparse
import hashlib
import json
import sympy as sp

HERE=Path(__file__).resolve().parent
CERT=HERE/'endpoint_root_unity_v38_certificate.json'
t=sp.Symbol('t')

def norm_check(ell):
    phi=sp.Poly(sp.cyclotomic_poly(ell,t),t,domain=sp.QQ)
    one=sp.Poly(1,t,domain=sp.QQ)
    zero=sp.Poly(0,t,domain=sp.QQ)
    coeff=[one]
    for i in range(ell):
        power=sp.Poly(t**(2*i+1),t,domain=sp.QQ).rem(phi)
        nxt=[zero for _ in range(len(coeff)+1)]
        for k,c in enumerate(coeff):
            nxt[k]=(nxt[k]-c).rem(phi)
            nxt[k+1]=(nxt[k+1]-c*power).rem(phi)
        coeff=nxt
    expected=[0]*(ell+1)
    if ell%2:
        expected[0]=-1;expected[ell]=-1
    else:
        expected[0]=1;expected[ell//2]=2*(-1)**(ell//2);expected[ell]=1
    assert all(c==sp.Poly(a,t,domain=sp.QQ) for c,a in zip(coeff,expected))
    # Coefficients multiply Q^(ell-k) z^k, with z=beta*x^2.
    zero_edges=[i for i in range(ell) if (2*i)%ell==0]
    assert len(zero_edges)==sp.gcd(2,ell)
    half_norm=None
    if ell%2==0:
        d=ell//2
        halves=[]
        for sign in (1,-1):
            cc=[one]
            for i in range(d):
                power=sp.Poly(t**((sign*(2*i+1))%ell),t,domain=sp.QQ).rem(phi)
                nn=[zero for _ in range(len(cc)+1)]
                for k,c in enumerate(cc):
                    nn[k]=(nn[k]-c).rem(phi)
                    nn[k+1]=(nn[k+1]-c*power).rem(phi)
                cc=nn
            halves.append(cc)
        hh=[0]*(d+1);hh[0]=(-1)**d;hh[d]=1
        assert halves[0]==halves[1]
        assert all(c==sp.Poly(a,t,domain=sp.QQ) for c,a in zip(halves[0],hh))
        assert sp.Poly(t**d+1,t,domain=sp.QQ).rem(phi).is_zero
        half_norm={'u^d_v^d_and_v^d_u^d_coefficients':hh,
                   'half_powers_commute':True,'t^d_equals_minus_one':True}
    return {'order':ell,'cyclotomic_polynomial':str(phi.as_expr()),
            'norm_coefficients':expected,'zero_edges_in_one_orbit':zero_edges,
            'exact_coefficient_ring':'QQ[t]/cyclotomic_polynomial',
            'norm_identity_passed':True,'even_McKay_half_norm':half_norm}

def mckay_special_fiber():
    # QQ[a,b]/(a^2,ab,b^2) # C2, with g negating a,b.
    basis=[(m,g) for m in range(3) for g in range(2)]
    def add(p,q):
        r=p.copy()
        for k,c in q.items():r[k]=r.get(k,sp.Rational(0))+c
        return {k:c for k,c in r.items() if c}
    def multiply(p,q):
        out={}
        for (m,g),c in p.items():
            for (n,h),a in q.items():
                if m and n:continue
                k=(m or n,(g+h)%2)
                out[k]=out.get(k,sp.Rational(0))+c*a*((-1)**g if n else 1)
        return {k:c for k,c in out.items() if c}
    ep={(0,0):sp.Rational(1,2),(0,1):sp.Rational(1,2)}
    em={(0,0):sp.Rational(1,2),(0,1):sp.Rational(-1,2)}
    aa={(1,0):sp.Rational(1)};bb={(2,0):sp.Rational(1)}
    images={'e0':ep,'e1':em,'a0':multiply(aa,ep),'a1':multiply(bb,ep),
            'b0':multiply(aa,em),'b1':multiply(bb,em)}
    ends={'e0':(0,0),'e1':(1,1),'a0':(0,1),'a1':(0,1),'b0':(1,0),'b1':(1,0)}
    mat=sp.Matrix([[p.get(k,0) for p in images.values()] for k in basis])
    assert mat.rank()==6
    for r,pr in images.items():
        for s,ps in images.items():
            expected={}
            if ends[r][0]==ends[s][1]:
                if r.startswith('e'):expected=ps
                elif s.startswith('e'):expected=pr
            assert multiply(pr,ps)==expected
    return {'dimension':6,'idempotents':'(1+g)/2, (1-g)/2',
            'four_arrows':'a*e0,b*e0,a*e1,b*e1',
            'exact_basis_change_determinant':str(mat.det()),
            'all_36_multiplication_pairs_checked':True,
            'matrix_model':'(QQ[a,b]/(a^2,ab,b^2)) # C2',
            'isomorphic_to_two_vertex_radical_square_zero_model':True}

def normalized_fiber(ell):
    """Faithful matrix model of the quiver after all nonzero edges are scaled.

    Keys (r,i,j) are matrix units over a basic algebra. Odd order has the basic
    algebra QQ; even order has two idempotents and four radical arrows, with
    all products of two radical arrows zero. Each original vertex and both
    orientations of every edge are constructed and all defining path relations
    checked. Their multiplicative closure reaches every basis unit, proving
    the required lower bound independently of a normal-form upper bound.
    """
    even=ell%2==0
    size=ell//2 if even else ell
    # (source,target), with two arrows in each direction.
    endpoints={'e0':(0,0)}
    if even:
        endpoints.update(e1=(1,1),a0=(0,1),a1=(0,1),b0=(1,0),b1=(1,0))
    radical={r for r in endpoints if not r.startswith('e')}

    def basic_mul(r,s):
        sr,tr=endpoints[r];ss,ts=endpoints[s]
        if sr!=ts or (r in radical and s in radical):return None
        if r.startswith('e'):return s
        if s.startswith('e'):return r
        raise AssertionError('Unaccounted basic product')

    def mul(a,b):
        if a is None or b is None:return None
        r,i,j=a;s,k,l=b
        if j!=k:return None
        out=basic_mul(r,s)
        return None if out is None else (out,i,l)

    vertices=[]
    for i in range(ell):
        comp=i//size if even else 0
        vertices.append(('e'+str(comp),i%size,i%size))
    us=[];vs=[];weights=[]
    for i in range(ell):
        target=(i+1)%ell
        if not even:
            if i==ell-1:u=v=None;weight=0
            else:u=('e0',target,i);v=('e0',i,target);weight=1
        elif i==size-1:
            u=('a0',0,size-1);v=('b0',size-1,0);weight=0
        elif i==ell-1:
            u=('b1',0,size-1);v=('a1',size-1,0);weight=0
        else:
            r='e'+str(i//size)
            u=(r,target%size,i%size);v=(r,i%size,target%size);weight=1
        us.append(u);vs.append(v);weights.append(weight)
        assert mul(u,v)==(vertices[target] if weight else None)
        assert mul(v,u)==(vertices[i] if weight else None)

    for start in range(ell):
        p=vertices[start]
        for k in range(ell):p=mul(us[(start+k)%ell],p)
        assert p is None
        p=vertices[start]
        for k in range(ell):p=mul(vs[(start-k-1)%ell],p)
        assert p is None

    gens=[g for g in vertices+us+vs if g is not None]
    reached=set(gens);todo=deque(gens)
    while todo:
        a=todo.popleft()
        for g in gens:
            b=mul(g,a)
            if b is not None and b not in reached:
                reached.add(b);todo.append(b)
    full={(r,i,j) for r in endpoints for i in range(size) for j in range(size)}
    assert reached==full
    rad={a for a in full if a[0] in radical}
    assert all(mul(a,b) is None for a in rad for b in rad)
    expected=6*size*size if even else ell*ell
    assert len(reached)==expected
    assert len(rad)==(4*size*size if even else 0)
    # Removing zero edges gives one ell-vertex or two d-vertex matrix blocks.
    comps=[size,size] if even else [ell]
    return {'order':ell,'normalized_edge_weights':weights,
            'matrix_block_sizes':comps,'generated_algebra_dimension':len(reached),
            'radical_dimension':len(rad),'radical_square_zero':True,
            'simple_module_dimensions':comps,
            'all_backtracking_and_full_cycle_relations_passed':True,
            'multiplicative_closure_reaches_full_model_basis':True,
            'model':'M_d(two_vertex_four_arrow_radical_square_zero)' if even else 'M_ell(QQ)'}

def compute():
    norms=[norm_check(ell) for ell in range(3,21)]
    fibers=[normalized_fiber(ell) for ell in range(3,17)]
    Q,X,U,V,beta,F=sp.symbols('Q X U V beta F')
    local_equation=U*V-F**2
    hessian=sp.hessian(local_equation,(U,V,F))
    assert hessian.det()==2
    # Every parameter here is exact. Floating root-of-unity tests are absent.
    return {'version':38,'status':'PASS','scope':'root-of-unity central chart and even-order etale McKay model',
            'norm_identity_checks':norms,'finite_fiber_models':fibers,
            'McKay_special_fiber':mckay_special_fiber(),
            'transverse_A1_hessian':[[str(z) for z in row] for row in hessian.tolist()],
            'transverse_A1_hessian_determinant':str(hessian.det()),
            'proof_inputs':{'central_localization':'Xi=x^ell, S[Xi^-1]=B[x^-1][J]',
              'odd_center':'UV=-Q^ell-beta^ell Xi^2',
              'even_center':'UV=(Q^(ell/2)+(-1)^(ell/2) beta^(ell/2) Xi)^2',
              'odd_Azumaya':'entire central chart',
              'even_non_Azumaya':'U=V=Q^(ell/2)+(-1)^(ell/2) beta^(ell/2) Xi=0',
              'even_etale_cover':'lambda^ell=Xi; T=C[Q,lambda^+-1,J,P,R]/(PR-((-1)^d Q^d+beta^d lambda^(2d)))',
              'even_etale_Morita':'A after etale base change Morita equivalent to T#C2',
              'formal_singular_model':'M_d(C[[a,b,z1,z2]]#C2), action negates a,b and fixes z1,z2',
              'higher_order_proof':'cyclic norm and invertible-edge contraction, all ell'},
            'not_claimed':['global center along Xi=0','derived equivalence classification'],
            'exact_arithmetic_only':True}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check',action='store_true')
    p.add_argument('--write-certificate',action='store_true')
    args=p.parse_args()
    if args.check and args.write_certificate:p.error('Choose one mode')
    before=hashlib.sha256(CERT.read_bytes()).hexdigest() if CERT.exists() else None
    result=compute()
    if args.write_certificate:
        CERT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    else:
        if not CERT.exists():raise SystemExit('Certificate absent; normal mode never writes it')
        assert result==json.loads(CERT.read_text()),'Frozen certificate mismatch'
        assert hashlib.sha256(CERT.read_bytes()).hexdigest()==before
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__=='__main__':main()
