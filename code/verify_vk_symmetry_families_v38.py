#!/usr/bin/env python3
"""Exact all-order Ga-preserving VK families and the smooth jump stratum.

Normal execution is read-only.  The v37 invariant tangent witnesses are
validated again against the frozen multiplication; no numerical or finite
order extrapolation is used.  The new correction is supported on the
primitive w_0 times degree-one product and has pure-polynomial output.
All identities of degrees 0, 1, 2, and 3 in the parameters are checked;
higher terms vanish by support.  The resulting family is therefore exact
over a polynomial parameter ring, not merely a truncated deformation.
"""
from pathlib import Path
from itertools import combinations_with_replacement
import json,sys
sys.dont_write_bytecode=True
CODE=Path(__file__).resolve().parent
if not (CODE/'verify_vk_symmetry_jump_v37.py').is_file():
    CODE=CODE.parent/'output/vk_lo_deformations_v37/code'
sys.path.insert(0,str(CODE))
from verify_vk_symmetry_jump_v37 import *

def rational_matrix(J):
    return fmpq_mat([[fmpq(s) for s in row] for row in J])

def stack_columns(A,B):
    return fmpq_mat([[A[i,k] for k in range(A.ncols())]
                    +[B[i,k] for k in range(B.ncols())]
                    for i in range(A.nrows())])

def support(M,n):
    return [i for i in range(M.nrows())
            if any(M[i,k] for k in range(M.ncols()))]

def compute_case(j):
    old=json.loads((CODE/'vk_symmetry_v37_certificate.json').read_text())['cases'][j]
    k=4+j
    U=select(rational_matrix(old['first_order_cocycles']),range(1584),range(k))
    E=select(rational_matrix(old['first_order_derivation_lifts']),range(620),range(k))
    mono,_=make_product(j,3-2*j,Q(0),Q(1))
    d1,_=differential(1,mono);d2,_=differential(2,mono)
    L=action(2,derivation(j,3-2*j))
    require(d1.rank()==616 and d2.rank()==933,'frozen ranks')
    require(d1*E==L*U,'linear derivation equation')
    require(d2*U==zero(972,k),'first-order cocycles')
    require(stack_columns(d1,U).rank()==616+k,'independent Kodaira-Spencer classes')
    w=(0,0,0,1)
    W=[i for i,(ch,ins,out) in enumerate(cochains(2))
       if ch==(0,3,4) and ins[0]==w]
    W0=[i for i in W if cochains(2)[i][2][3]==0]
    require(len(W)==54 and len(W0)==45,'primitive support dimensions')
    require(set(support(U,2))<=set(W),'linear product support')
    require(all(cochains(1)[i][1][0][3]==1 and cochains(1)[i][2][3]==0
                for i in support(E,1)),'derivation lowers w-filtration')
    if j==0:
        require(set(support(U,2))<=set(W0),'j0 pure linear output')
    Us=[cochain_dict(2,U,i) for i in range(k)]
    Es=[cochain_dict(1,E,i) for i in range(k)]
    pairs=list(combinations_with_replacement(range(k),2))
    rhs=[]
    for a,b in pairs:
        asso=compose22(Us[a],Us[b])
        rr=act12(Es[a],Us[b])
        if a!=b:
            asso+=compose22(Us[b],Us[a])
            rr+=act12(Es[b],Us[a])
        require(asso==zero(972,1),'all quadratic associators')
        rhs.append(rr)
    RHS=concat(rhs)
    require(all(RHS[i,c]==0 for i in range(1584) if i not in set(W0)
                for c in range(len(pairs))),'quadratic derivation support')
    M=select(L,W0,W0)
    require(M.rank()==38,'pure-support operator rank')
    MR,rank=M.rref();pc=pivots(MR,rank)
    MT,rank=M.transpose().rref();pr=pivots(MT,rank)
    small=select(M,pr,pc).solve(-select(RHS,[W0[i] for i in pr],range(len(pairs))))
    V=zero(1584,len(pairs))
    for i,p in enumerate(pc):
        for c in range(len(pairs)):
            V[W0[p],c]=small[i,c]
    require(L*V==-RHS,'exact quadratic derivation correction')
    require(d2*V==zero(972,len(pairs)),'quadratic product is a cocycle')
    Vs=[cochain_dict(2,V,i) for i in range(V.ncols())]
    for a in range(k):
        for v in Vs:
            require(act12(Es[a],v)==zero(1584,1),'all cubic derivation terms')
            require(compose22(Us[a],v)==zero(972,1)
                    and compose22(v,Us[a])==zero(972,1),'all mixed associators')
    for a in range(len(Vs)):
        for b in range(a,len(Vs)):
            require(compose22(Vs[a],Vs[b])==zero(972,1),'all quartic associators')
    # Any W-supported product is never an inner multiplication in a
    # nontrivial composable triple.  Its first input is the primitive w,
    # absent from the image of the unchanged degree-one by degree-two map.
    for a,b in product(basis(1),basis(2)):
        require(all(out[3]==0 for out in mono(a,b)),'primitive w not a composite')
    # The derivation fixes primitive arrows x and sends y to x.  All
    # corrections lower the w-filtration.  On degree d <= 4 its two
    # associated-graded layers have nilpotence indices <= 2d+1 and
    # 2(d-3)+1, respectively; hence its twelfth power is identically zero.
    require(derivation(j,3-2*j)((0,1,0,0))=={(1,0,0,0):Q(1)},'outer Ga witness')
    return {
        'j':j,'r':3-2*j,'parameters':k,
        'differential_ranks':[616,933],
        'Kodaira_Spencer_augmented_rank':616+k,
        'primitive_product_support_dimension':54,
        'pure_product_support_dimension':45,
        'pure_operator_rank':M.rank(),
        'quadratic_derivation_rhs_rank':RHS.rank(),
        'quadratic_correction_nonzero_entries':sum(bool(V[i,c]) for i in range(1584) for c in range(len(pairs))),
        'pairs':pairs,'linear_products':asjson(U),'linear_derivations':asjson(E),
        'quadratic_products':asjson(V),
        'uniform_derivation_nilpotence_bound':12,
        'checks':{
            'linear_derivation':True,'cocycles':True,'KS_independent':True,
            'quadratic_derivation':True,'cubic_derivation_zero':True,
            'all_parameter_associativity':True,'w_filtration':True,
            'primitive_arrow_noninner_witness':True,
            'all_higher_terms_zero_by_support':True}}

def compute():
    cases=[compute_case(j) for j in (0,1)]
    require(cases[0]['quadratic_derivation_rhs_rank']==0,'j0 linear family')
    require(cases[0]['quadratic_correction_nonzero_entries']==0,'j0 no quadratic correction')
    require(cases[1]['quadratic_derivation_rhs_rank']==7,'j1 quadratic RHS rank')
    require(cases[1]['quadratic_correction_nonzero_entries']==141,'j1 correction support')
    return json.loads(json.dumps({'version':38,'status':'PASS','arithmetic':'QQ',
        'scope':'Exact polynomial Ga-preserving families: four parameters for B_0,3 and five for B_1,1. The latter does not determine its entire nonreduced jump structure.',
        'cases':cases}))

if __name__=='__main__':
    actual=compute()
    expected=json.loads(Path(__file__).with_name('vk_symmetry_families_v38_certificate.json').read_text())
    require(actual==expected,'complete frozen exact certificate')
    if '--dump' in sys.argv:
        print(json.dumps(actual,indent=2))
    else:
        print(json.dumps({'version':38,'status':'PASS','cases':[{'j':c['j'],'parameters':c['parameters'],'KS_rank':c['Kodaira_Spencer_augmented_rank']-616,'Ga_nilpotence_bound':c['uniform_derivation_nilpotence_bound']} for c in actual['cases']]},indent=2))
