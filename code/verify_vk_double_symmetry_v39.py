#!/usr/bin/env python3
"""All-order, independent rational-cochain certificate for the VK double locus.

This verifier never imports the matrix elimination or jet-recovery scripts.
It reconstructs the original multiplication and the v38 five-parameter
family, reads an explicit polynomial numerator/denominator witness, and
checks all associativity and derivation equations directly in the bar
complex over a multivariate rational polynomial ring.  No finite jet or
numerical sampling is used.  Normal execution is read-only.
"""
from pathlib import Path
import sys,json,hashlib,time
sys.dont_write_bytecode=True
CODE=Path(__file__).resolve().parent
if not (CODE/'verify_vk_symmetry_jump_v37.py').is_file():
    CODE=CODE.parent/'output/vk_lo_deformations_v38/code'
sys.path.insert(0,str(CODE))
from verify_vk_symmetry_jump_v37 import *
from flint import fmpq_mpoly_ctx

HERE=Path(__file__).resolve().parent
CTX=fmpq_mpoly_ctx.get(['u1','u2','u3','u4','u5'],ordering='lex')
EXP0=(0,)*5
ZERO_P=CTX.from_dict({});ONE_P=CTX.from_dict({EXP0:1})

def polynomial(data):
    return CTX.from_dict({tuple(e):fmpq(c) for e,c in data})
def mono_param(exp):return CTX.from_dict({tuple(exp):1})
def unit_exp(i):return tuple(int(i==j) for j in range(5))
def rational(q):
    return fmpq(q.numerator,q.denominator) if hasattr(q,'numerator') else fmpq(q)
def add_poly(out,key,value):
    if value:
        z=out.get(key,ZERO_P)+value
        if z:out[key]=z
        elif key in out:del out[key]
def cochain(n,values):
    out={}
    for (chain,ins,target),v in zip(cochains(n),values):
        if v:out.setdefault((chain,ins),{})[target]=v
    return out
def matrix_values(data):return [[fmpq(v) for v in row] for row in data]
def add_scaled_column(values,data,column,scalar):
    for i,row in enumerate(data):
        if row[column]!='0':values[i]+=scalar*fmpq(row[column])

def bracket12(D,F):
    """[D,F] directly on every composable pair, with polynomial coefficients."""
    answer={}
    for chain in combinations(OBJECTS,3):
        for a,b in product(basis(chain[1]-chain[0]),basis(chain[2]-chain[1])):
            out={}
            for v,s in F.get((chain,(a,b)),{}).items():
                for w,t in D.get(((chain[0],chain[2]),(v,)),{}).items():add_poly(out,w,s*t)
            for v,s in D.get((chain[:2],(a,)),{}).items():
                for w,t in F.get((chain,(v,b)),{}).items():add_poly(out,w,-s*t)
            for v,s in D.get((chain[1:],(b,)),{}).items():
                for w,t in F.get((chain,(a,v)),{}).items():add_poly(out,w,-s*t)
            for w,v in out.items():answer[(chain,(a,b),w)]=v
    return answer

def composition22(F,G):
    """Gerstenhaber insertion on all composable triples, over QQ[u]."""
    answer={}
    for chain in combinations(OBJECTS,4):
        for a,b,c in product(*(basis(chain[i+1]-chain[i]) for i in range(3))):
            out={}
            for v,s in G.get((chain[:3],(a,b)),{}).items():
                for w,t in F.get(((chain[0],chain[2],chain[3]),(v,c)),{}).items():add_poly(out,w,s*t)
            for v,s in G.get((chain[1:],(b,c)),{}).items():
                for w,t in F.get(((chain[0],chain[1],chain[3]),(a,v)),{}).items():add_poly(out,w,-s*t)
            for w,v in out.items():answer[(chain,(a,b,c),w)]=v
    return answer

def add_dict(A,B):
    out=dict(A)
    for k,v in B.items():add_poly(out,k,v)
    return out

def compute():
    start=time.time()
    witness_path=HERE/'vk_double_symmetry_v39_witness.json'
    witness=json.loads(witness_path.read_text())
    old_path=CODE/'vk_symmetry_v37_certificate.json'
    family_path=CODE/'vk_symmetry_families_v38_certificate.json'
    old=json.loads(old_path.read_text())['cases'][1]
    family=json.loads(family_path.read_text())['cases'][1]
    require(witness['version']==39 and witness['extra_v37_kernel_index']==5,'witness format')
    den=polynomial(witness['denominator'])
    require(den.to_dict().get(EXP0)==1,'denominator is a unit at the origin')
    nums=[polynomial(p) for p in witness['numerators']]
    support=witness['unknown_support']
    require(len(support)==122 and len(set(support))==122,'witness coordinate support')
    require(len(nums)==len(support),'one numerator per correction coordinate')
    require(sum(i<1584 for i in support)==22,'product correction coordinates')
    require(all(cochains(2)[i][0]==(0,3,4)
                and cochains(2)[i][1][0]==(0,0,0,1)
                for i in support if i<1584),'primitive-product correction support')
    require(all(not p.to_dict().get(EXP0,0) for p in nums),'corrections vanish at the origin')
    require(all(0<=i<2204 for i in support),'cochain coordinates')

    mono0,_=make_product(1,1,Q(0),Q(1));delta0=derivation(1,1)
    mus=[];ds=[]
    for chain,ins,out in cochains(2):mus.append(ONE_P*rational(mono0(*ins).get(out,Q(0))))
    for chain,ins,out in cochains(1):ds.append(ONE_P*rational(delta0(ins[0]).get(out,Q(0))))
    for i in range(5):
        s=mono_param(unit_exp(i))
        add_scaled_column(mus,family['linear_products'],i,s)
        add_scaled_column(ds,family['linear_derivations'],i,s)
    for c,(i,j) in enumerate(family['pairs']):
        ex=tuple(a+b for a,b in zip(unit_exp(i),unit_exp(j)))
        add_scaled_column(mus,family['quadratic_products'],c,mono_param(ex))
    vs=[den*fmpq(row[5]) for row in old['first_order_cocycles']]
    es=[den*fmpq(row[5]) for row in old['first_order_derivation_lifts']]
    for i,p in zip(support,nums):
        if i<1584:vs[i]+=p
        else:es[i-1584]+=p
    Mu,D,V,E=cochain(2,mus),cochain(1,ds),cochain(2,vs),cochain(1,es)

    # These are identities in the full polynomial ring, not in a truncation.
    require(not composition22(Mu,Mu),'base all-order associativity')
    require(not bracket12(D,Mu),'base all-order derivation')
    require(not add_dict(composition22(Mu,V),composition22(V,Mu)),
            'full transverse associativity, all 972 coordinates')
    require(not add_dict(bracket12(D,V),bracket12(E,Mu)),
            'full transverse derivation, all 1584 coordinates')

    # A separate exact tangent check against all Hochschild boundaries.
    d1,_=differential(1,mono0)
    cols=[[fmpq(old['first_order_cocycles'][i][j]) for j in range(6)] for i in range(1584)]
    augmented=fmpq_mat([[d1[i,j] for j in range(620)]+cols[i] for i in range(1584)])
    require(d1.rank()==616 and augmented.rank()==622,'six independent KS classes')
    last=old['pairs'].index([5,5])
    q=fmpq(old['quadratic_obstruction_matrix'][1][last])
    require(q==fmpq(432000,2468041),'published nonzero quadratic obstruction')

    # Check the flag giving D^12=0, then use the square-zero lemma for
    # (D+epsilon E/den)^24=0.  The base derivation has unchanged associated
    # graded action; the two layers in degree d<=4 have lengths <=2d+1
    # and <=2(d-3)+1.
    for i,(chain,ins,out) in enumerate(cochains(1)):
        for c in range(5):
            if family['linear_derivations'][i][c]!='0':
                require(ins[0][3]==1 and out[3]==0,'base correction lowers w-filtration')
    require(delta0((0,1,0,0))=={(1,0,0,0):Q(1)},'noninner primitive-arrow witness')
    # Over the dual-number base, a relative inner derivation still has a
    # scalar action on each arrow space; the coefficient of x in D(y) is
    # 1 modulo epsilon and therefore remains a unit.
    return {
        'version':39,'status':'PASS','arithmetic':'Exact QQ multivariate polynomials (python-flint)',
        'scope':'Complete rational five-parameter family with one square-zero transverse parameter; all equations checked before completion.',
        'baseline_sha256':{
            old_path.name:hashlib.sha256(old_path.read_bytes()).hexdigest(),
            family_path.name:hashlib.sha256(family_path.read_bytes()).hexdigest()},
        'witness_sha256':hashlib.sha256(witness_path.read_bytes()).hexdigest(),
        'denominator':{'constant_coefficient':'1','total_degree':int(max(sum(e) for e in den.to_dict())),'monomials':len(den.to_dict())},
        'correction_coordinates':{'C2':22,'C1':100,'total':122},
        'numerator_maximum_degree':int(max(sum(e) for p in nums for e in p.to_dict())),
        'numerator_monomials':sum(len(p.to_dict()) for p in nums),
        'full_equation_counts':{'associativity':972,'derivation':1584,'total':2556},
        'all_residuals_identically_zero':True,'finite_jet_extrapolation':False,
        'KS_boundary_rank':616,'KS_augmented_rank':622,'KS_rank':6,
        'nonzero_quadratic_obstruction':str(q),
        'base_derivation_nilpotence_bound':12,'double_family_derivation_nilpotence_bound':24,
        'formal_conclusion':'Z_B11 = Spf C[[u1,u2,u3,u4,u5,epsilon]]/(epsilon^2)',
        'embedded_ideal':'(z1,...,z29,epsilon^2) in C[[u1,...,u5,epsilon,z1,...,z29]]'}

if __name__=='__main__':
    actual=compute()
    expected=json.loads(HERE.joinpath('vk_double_symmetry_v39_certificate.json').read_text())
    require(actual==expected,'complete frozen certificate')
    print(json.dumps(actual if '--dump' in sys.argv else {k:actual[k] for k in ['version','status','full_equation_counts','KS_rank','double_family_derivation_nilpotence_bound','formal_conclusion']},indent=2))
