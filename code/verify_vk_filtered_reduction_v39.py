#!/usr/bin/env python3
"""Exact filtered reduction of the two quantum VK deformation problems.

Normal execution is read-only.  It verifies the quotient Hochschild complex,
the primitive relative complex, their exact cohomology sequence, and the
one-parameter symmetry-preserving pure family.  All calculations use QQ or
QQ(gamma); no finite-jet extrapolation is made.
"""
from pathlib import Path
from functools import lru_cache
import sys, json
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CODE = HERE if (HERE/'verify_vk_symmetry_jump_v37.py').is_file() else HERE.parent/'output/vk_lo_deformations_v38/code'
sys.path.insert(0, str(CODE))
from verify_vk_symmetry_jump_v37 import *


def identity(n):
    out = zero(n,n)
    for i in range(n): out[i,i] = 1
    return out


def stack(A, B):
    return fmpq_mat([[A[i,k] for k in range(A.ncols())] +
                     [B[i,k] for k in range(B.ncols())]
                     for i in range(A.nrows())])


def embed(A, rows, n):
    out = zero(n, A.ncols())
    for i,r in enumerate(rows):
        for c in range(A.ncols()):
            out[r,c] = A[i,c]
    return out


def quotient_coordinates(B):
    """Quotient of the row ambient vector space by the column span of B."""
    R, rank = B.transpose().rref()
    ps = pivots(R, rank)
    fs = [i for i in range(B.nrows()) if i not in set(ps)]
    P = zero(len(fs), B.nrows())
    for k,f in enumerate(fs):
        P[k,f] = 1
        for i,p in enumerate(ps):
            P[k,p] = -R[i,f]
    require(P*B == zero(len(fs), B.ncols()), 'quotient annihilates boundaries')
    return P


def cohomology2(d1, d2):
    R, b = d1.transpose().rref()
    ps = pivots(R,b)
    fs = [i for i in range(d1.nrows()) if i not in set(ps)]
    df = select(d2, range(d2.nrows()), fs)
    Z, zr = df.rref()
    zp = pivots(Z,zr)
    zf = [i for i in range(len(fs)) if i not in set(zp)]
    V = zero(len(fs),len(zf))
    for k,c in enumerate(zf):
        V[c,k] = 1
        for i,p in enumerate(zp):
            V[p,k] = -Z[i,c]
    Rfree = select(R,range(b),fs).transpose()
    def classes(W):
        Wf = select(W,fs,range(W.ncols()))-Rfree*select(W,ps,range(W.ncols()))
        hh = select(Wf,zf,range(W.ncols()))
        require(Wf == V*hh, 'input is a Hochschild cocycle')
        return hh
    U = embed(V,fs,d1.nrows())
    require(d2*U == zero(d2.nrows(),len(zf)), 'cohomology representatives')
    return U, classes


def compute_case(j):
    mono,_ = make_product(j,3-2*j,Q(0),Q(1))
    def product_rank(dl,dr):
        bs = [b for b in basis(dl+dr) if not b[3]]
        rr = {b:i for i,b in enumerate(bs)}
        pairs = list(product([a for a in basis(dl) if not a[3]],
                             [b for b in basis(dr) if not b[3]]))
        mat = zero(len(bs),len(pairs))
        for c,(a,b) in enumerate(pairs):
            for out,v in mono(a,b).items(): mat[rr[out],c] = fmpq(str(v))
        return mat.rank()
    pure4 = [b for b in basis(4) if not b[3]]
    r4 = {b:i for i,b in enumerate(pure4)}
    triples = list(product(basis(1),basis(2),basis(1)))
    triple_matrix = zero(15,len(triples))
    for col,(a,b,c) in enumerate(triples):
        for ab,ca in mono(a,b).items():
            for out,cb in mono(ab,c).items():
                triple_matrix[r4[out],col] += fmpq(str(ca*cb))
    intrinsic_ranks = [product_rank(1,2),product_rank(2,1),triple_matrix.rank()]
    require(intrinsic_ranks == [10,10,15], 'intrinsic pure composition images')
    d1,_ = differential(1,mono)
    d2,_ = differential(2,mono)
    F = {n:[i for i,(ch,ins,out) in enumerate(cochains(n))
            if out[3] <= sum(a[3] for a in ins)] for n in (1,2,3)}
    P = {n:[i for i,(ch,ins,out) in enumerate(cochains(n))
            if not out[3] and all(not a[3] for a in ins)] for n in (1,2,3)}
    Qc = {n:[i for i in range(len(cochains(n))) if i not in set(F[n])]
          for n in (1,2,3)}
    K = {n:[i for i in F[n] if i not in set(P[n])] for n in (1,2,3)}
    require([len(F[n]) for n in (1,2,3)] == [555,1368,810], 'filtered dimensions')
    require([len(P[n]) for n in (1,2,3)] == [479,1260,810], 'pure dimensions')
    require([len(Qc[n]) for n in (1,2,3)] == [65,216,162], 'quotient dimensions')
    require([len(K[n]) for n in (1,2,3)] == [76,108,0], 'relative dimensions')
    f1 = select(d1,F[2],F[1]); f2 = select(d2,F[3],F[2])
    q1 = select(d1,Qc[2],Qc[1]); q2 = select(d2,Qc[3],Qc[2])
    p1 = select(d1,P[2],P[1]); p2 = select(d2,P[3],P[2])
    k1 = select(d1,K[2],K[1])
    require(select(d1,Qc[2],F[1]) == zero(216,555), 'filtered d1 closure')
    require(select(d2,Qc[3],F[2]) == zero(162,1368), 'filtered d2 closure')
    require(select(d1,P[2],K[1]) == zero(1260,76), 'relative d1 closure')
    require(select(d2,F[3],K[2]) == zero(810,108), 'relative d2 zero')
    require(q2*q1 == zero(162,65), 'quotient complex')
    require([q1.rank(),q2.rank()] == [65,151], 'quotient H1 and H2 vanish')
    require([f1.rank(),f2.rank()] == [551,782], 'filtered ranks')
    require([p1.rank(),p2.rank()] == [475,782], 'pure ranks')
    require(k1.rank() == 76, 'no infinitesimal primitive stabilizer')
    left = [i for i in K[2] if cochains(2)[i][0] == (0,1,4)]
    right = [i for i in K[2] if cochains(2)[i][0] == (0,3,4)]
    require(len(left) == len(right) == 54, 'two primitive products')
    require(select(d1,left,K[1]).rank() == 54, 'left product gauge normalization')
    W = embed(identity(54),right,1584)
    W0rows = [i for i in right if cochains(2)[i][2][3] == 0]
    W0 = embed(identity(45),W0rows,1584)
    require(stack(k1,select(W,K[2],range(54))).rank() == 108,
            'right product surjects onto relative H2')
    UB,hB = cohomology2(d1,d2)
    UN,hN = cohomology2(p1,p2)
    require(UB.ncols() == 35 and UN.ncols() == 3, 'H2 dimensions')
    Wclass = hB(W)
    purelift = embed(UN,P[2],1584)
    Nclass = hB(purelift)
    require(Wclass.rank() == 32 and hB(W0).rank() == 24, 'primitive image ranks')
    require(stack(Wclass,Nclass).rank() == 35, 'exact H2 sequence')
    L = action(2,derivation(j,3-2*j))
    HB = hB(L*UB)
    HN = hN(select(L,P[2],P[2])*UN)
    PQ = quotient_coordinates(Wclass)
    rho = (PQ*Nclass).inv()*PQ
    require(rho*Wclass == zero(3,54), 'restriction kernel')
    require(rho*Nclass == identity(3), 'restriction surjection')
    require(rho*HB == HN*rho, 'equivariant cohomology sequence')
    WR,wr = Wclass.rref(); wp = pivots(WR,wr)
    WB = select(Wclass,range(35),wp)
    WT,wtr = WB.transpose().rref(); wpr = pivots(WT,wtr)
    HW = select(WB,wpr,range(wr)).solve(select(HB*WB,wpr,range(wr)))
    require(WB*HW == HB*WB, 'invariant primitive image')
    require(jordan(HN)['blocks'] == [3], 'pure action is one Jordan block')
    # The pure gamma family is independent of j.  Only pure products are used.
    from verify_vk_completion_symmetry_v38 import family
    ug = zero(1260,1)
    special = 0
    for l,i in enumerate(P[2]):
        chain,ins,out = cochains(2)[i]
        a,b = ins
        values = family(*chain,a,b)
        require(values[0] == mono(a,b), 'pure gamma special fibre')
        ug[l,0] = fmpq(str(values[1].get(out,Q(0))))
        special += 1
    gamma_class = hN(ug)
    require(gamma_class != zero(3,1), 'nonzero pure gamma tangent')
    require(HN*gamma_class == zero(3,1), 'pure gamma invariant tangent')
    invariant_restriction_rank = (rho*nullbasis(HB)).rank()
    require(invariant_restriction_rank == j, 'invariant pure direction lifts exactly for j1')
    # Connecting homomorphism ker L_N -> coker L_W in the snake sequence.
    connected = HB*Nclass*gamma_class
    connected_W = select(WB,wpr,range(wr)).solve(select(connected,wpr,[0]))
    require(WB*connected_W == connected, 'connecting class is primitive')
    connecting_class = quotient_coordinates(HW)*connected_W
    require((connecting_class == zero(connecting_class.nrows(),1)) == bool(j),
            'first-order primitive connecting obstruction')
    secondary_pure_zero = None
    if j == 1:
        old = json.loads((CODE/'vk_completion_symmetry_v38_certificate.json').read_text())
        previous = json.loads((CODE/'vk_symmetry_v37_certificate.json').read_text())['cases'][1]
        require(HB == fmpq_mat(previous['HH2_matrix']), 'frozen H2 coordinates agree')
        secondary = fmpq_mat(old['secondary_cohomology_coordinates'])
        require(quotient_coordinates(HB)*secondary != zero(6,1), 'nonzero known secondary class')
        secondary_pure_zero = quotient_coordinates(HN)*rho*secondary == zero(1,1)
        require(secondary_pure_zero, 'completion secondary class has zero pure image')
    return {
        'j':j,'r':3-2*j,
        'intrinsic_pure_composition_ranks':intrinsic_ranks,
        'filtered_dimensions':[555,1368,810], 'filtered_differential_ranks':[551,782],
        'quotient_dimensions':[65,216,162], 'quotient_differential_ranks':[65,151],
        'quotient_cohomology_H1_H2_H3':[0,0,11],
        'pure_dimensions':[479,1260,810], 'pure_differential_ranks':[475,782],
        'pure_HH_dimensions':[1,1,3,28],
        'relative_dimensions':[76,108,0], 'relative_d1_rank':76,
        'relative_HH1_HH2':[0,32], 'left_normalization_rank':54,
        'primitive_parameter_dimension':54,'primitive_gauge_dimension':22,
        'primitive_HH2_rank':32,'pure_output_primitive_HH2_rank':24,
        'primitive_HH2_Jordan':jordan(HW),'pure_HH2_Jordan':jordan(HN),
        'pure_HH2_action':asjson(HN),'pure_gamma_HH2_class':asjson(gamma_class),
        'invariant_restriction_rank':invariant_restriction_rank,
        'primitive_connecting_class_of_pure_gamma':asjson(connecting_class),
        'completion_secondary_pure_image_zero':secondary_pure_zero,
        'restriction_HH2_matrix':asjson(rho),'pure_HH2_lift_matrix':asjson(Nclass),
        'primitive_HH2_matrix':asjson(Wclass),
        'checks':{'filtered_subcomplex':True,'quotient_H1_H2_zero':True,
                  'primitive_relative_complex':True,'exact_HH2_sequence':True,
                  'equivariant_restriction':True,'pure_gamma_invariant_nonzero':True}}


def pure_family_symbolic():
    """All-order PBW and derivation identities, exactly in QQ(gamma)."""
    from sympy import Symbol, cancel
    g = Symbol('gamma')
    den = 1-g
    rules = {
        (1,0):{(0,1):(1+g)/den,(0,0):-1/den,(0,2):-2*g/den},
        (2,0):{(0,2):(1+g)/den,(0,1):-2/den,(0,0):1/den},
        (2,1):{(1,2):1,(0,1):1/den,(0,2):-1/den}}
    def put(out,w,c):
        v = cancel(out.get(w,0)+c)
        if v: out[w] = v
        elif w in out: del out[w]
    @lru_cache(None)
    def normal(w):
        for i in range(len(w)-1):
            pair = (w[i],w[i+1])
            if pair in rules:
                ans = {}
                for v,c in rules[pair].items():
                    for z,d in normal(w[:i]+v+w[i+2:]).items():
                        put(ans,z,c*d)
                return ans
        return {w:1}
    def multiply(p,q):
        ans = {}
        for u,c in p.items():
            for v,d in q.items():
                for z,e in normal(u+v).items(): put(ans,z,c*d*e)
        return ans
    def subtract(p,q):
        ans = dict(p)
        for z,c in q.items(): put(ans,z,-c)
        return ans
    D = {0:{},1:{(0,):1,(2,):2*g},2:{(1,):2}}
    def derivative(p):
        ans = {}
        for w,c in p.items():
            for i,l in enumerate(w):
                for v,d in D[l].items():
                    for z,e in normal(w[:i]+v+w[i+1:]).items():
                        put(ans,z,c*d*e)
        return ans
    require(subtract(multiply(rules[2,1],{(0,):1}),
                     multiply({(2,):1},rules[1,0])) == {}, 'all-order pure PBW overlap')
    for pair,rhs in rules.items():
        require(subtract(derivative({pair:1}),derivative(rhs)) == {},
                'all-order pure derivation relation')
    return {'coefficient_ring':'QQ[gamma,(1-gamma)^-1]',
            'PBW_overlap_word':[2,1,0], 'PBW_overlap_zero':True,
            'quadratic_derivation_relations_checked':3,
            'derivation_on_x_y_Z':['0','x+2*gamma*Z','2*y'],
            'degree_one_characteristic_polynomial':'z*(z^2-4*gamma)'}


def compute():
    return {'version':39,'status':'PASS','arithmetic':'QQ and QQ(gamma)',
            'scope':'All formal marked VK deformations and derivation lifts admit the w-filtration; primitive relative deformation space is smooth of dimension 32. The pure symmetry locus is a smooth curve. The final doubled fivefold theorem is verified separately.',
            'cases':[compute_case(j) for j in (0,1)],
            'pure_family':pure_family_symbolic()}


if __name__ == '__main__':
    actual = compute()
    if '--dump' in sys.argv:
        print(json.dumps(actual,indent=2,sort_keys=True))
    else:
        expected = json.loads(HERE.joinpath('vk_filtered_reduction_v39_certificate.json').read_text())
        require(actual == expected,'frozen exact filtered certificate')
        print(json.dumps({'version':39,'status':'PASS',
                          'cases':[{k:c[k] for k in ['j','quotient_cohomology_H1_H2_H3',
                                    'relative_HH1_HH2','pure_HH_dimensions']}
                                   for c in actual['cases']],
                          'all_order_pure_family':actual['pure_family']},indent=2))
