#!/usr/bin/env python3
"""Exact cochain verification of the enhanced obstruction transgression.

Read-only normal execution; --dump emits the computed certificate.  The
general naturality theorem is proved in the accompanying manuscript. This
gate verifies its signed cone identities, gauge-choice identities and the
nonzero VK image on the original rational four-object bar complex.
"""
from pathlib import Path
import sys, json, hashlib
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CODE = HERE if (HERE/'verify_vk_symmetry_jump_v37.py').is_file() else HERE.parent/'baseline_v39/vk_lo_deformations_v39/code'
sys.path.insert(0, str(CODE))
from verify_vk_symmetry_jump_v37 import *

def digest_vector(V):
    return hashlib.sha256(json.dumps(asjson(V), separators=(',', ':')).encode()).hexdigest()

def bracket11(P, Q1):
    rows = {v:i for i,v in enumerate(cochains(1))}
    ans = zero(len(rows), 1)
    for chain in combinations(OBJECTS, 2):
        for a in basis(chain[1]-chain[0]):
            p = {}
            for b,c in Q1.get((chain,(a,)),{}).items():
                for z,e in P.get((chain,(b,)),{}).items(): accum(p,z,c*e)
            for b,c in P.get((chain,(a,)),{}).items():
                for z,e in Q1.get((chain,(b,)),{}).items(): accum(p,z,-c*e)
            for z,c in p.items(): ans[rows[(chain,(a,),z)],0] = c
    return ans

def compute():
    p38 = CODE/'vk_completion_symmetry_v38_certificate.json'
    p37 = CODE/'vk_symmetry_v37_certificate.json'
    old = json.loads(p38.read_text())
    prior = next(c for c in json.loads(p37.read_text())['cases'] if c['j']==1)
    U = fmpq_mat(old['completion_tangent_cochain'])
    Eta = fmpq_mat(old['derivation_first_correction'])
    V = fmpq_mat(old['associativity_second_correction'])
    mono,_ = make_product(1,1,Q(0),Q(1))
    delta = derivation(1,1)
    d1,_ = differential(1,mono)
    d2,_ = differential(2,mono)
    L1,L2,L3 = [action(n,delta) for n in (1,2,3)]
    require(d2*U == zero(d2.nrows(),1), 'U is a cocycle')
    require(d1*Eta == L2*U, 'first derivation correction')
    O = compose22(cochain_dict(2,U),cochain_dict(2,U))
    QQ = act12(cochain_dict(1,Eta),cochain_dict(2,U))
    require(-d2*QQ == L3*O, 'enhanced obstruction is a cone cocycle')
    require(d2*V == O, 'ordinary corner obstruction nullhomotopy')
    q = L2*V+QQ
    require(d2*q == zero(d2.nrows(),1), 'transgression is a Hochschild cocycle')

    # Independently reconstruct the boundary-pivot quotient and cokernel.
    R,br = d1.transpose().rref(); ps=pivots(R,br)
    fs=[i for i in range(d1.nrows()) if i not in set(ps)]
    df=select(d2,range(d2.nrows()),fs); Z,zr=df.rref(); zp=pivots(Z,zr)
    zf=[i for i in range(len(fs)) if i not in set(zp)]
    lifts=zero(len(fs),len(zf))
    for k,c in enumerate(zf):
        lifts[c,k]=1
        for i,p in enumerate(zp):lifts[p,k]=-Z[i,c]
    RF=select(R,range(br),fs).transpose()
    def hclass(A):
        Af=select(A,fs,range(A.ncols()))-RF*select(A,ps,range(A.ncols()))
        H=select(Af,zf,range(A.ncols()))
        require(Af==lifts*H,'cocycle quotient reconstruction')
        return H
    H=fmpq_mat(prior['HH2_matrix']); HR,hr=H.transpose().rref(); hp=pivots(HR,hr)
    hf=[i for i in range(35) if i not in set(hp)]
    hq=hclass(q)
    cq=select(hq,hf,[0])-select(HR,range(hr),hf).transpose()*select(hq,hp,[0])
    require(asjson(hq)==old['secondary_cohomology_coordinates'],'HH2 image')
    require(asjson(cq)==old['symmetry_quadratic_obstruction'],'cokernel transgression')
    require(cq[1,0]==120,'nonzero obstruction-line map')

    # Changing the first derivation correction by a closed cochain changes
    # the enhanced class by a cone boundary. Vertex diagonal inner
    # derivations act trivially on E-relative cochains.
    D=zero(len(cochains(1)),1); Inn=zero(len(cochains(1)),1)
    for i,(chain,ins,out) in enumerate(cochains(1)):
        D[i,0]=fmpq(str(delta(ins[0]).get(out,Q(0))))
        if ins[0]==out: Inn[i,0]=chain[1]**2-chain[0]**2
    Eta2=Eta+3*D+Inn
    require(d1*Eta2==d1*Eta,'closed difference of derivation corrections')
    QQ2=act12(cochain_dict(1,Eta2),cochain_dict(2,U))
    require(QQ2-QQ==3*d1*Eta,'derivation-choice cone boundary')

    # Explicit representative-change identity. It is the degree-two gauge
    # identity, not a test of a precomputed new obstruction matrix.
    F=zero(len(cochains(1)),1)
    for i in range(0,F.nrows(),37):F[i,0]=fmpq((i%11)-5,7)
    dF=d1*F; LF=L1*F
    U2=U+dF; Eta3=Eta+LF
    require(d1*Eta3==L2*U2,'gauge-changed first pair')
    O2=compose22(cochain_dict(2,U2),cochain_dict(2,U2))
    QQ3=act12(cochain_dict(1,Eta3),cochain_dict(2,U2))
    FD=cochain_dict(1,F)
    X=act12(FD,cochain_dict(2,U))+fmpq(1,2)*act12(FD,cochain_dict(2,dF))
    Y=-bracket11(cochain_dict(1,Eta),FD)+fmpq(1,2)*bracket11(FD,cochain_dict(1,LF))
    require(-d2*X==O2-O,'first component of gauge cone boundary')
    require(L2*X-d1*Y==QQ3-QQ,'second component of gauge cone boundary')
    return {
        'version':40,'status':'PASS','arithmetic':'QQ; Fraction and python-flint fmpq_mat',
        'scope':'Signed mapping-cone transgression and choice identities on B_(1,1); source existence and functoriality are general proofs.',
        'input_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (p37,p38)},
        'cochain_dimensions':[620,1584,972],
        'cone_degree_three_dimension':2556,
        'checks':{
            'first_order_pair':True,'enhanced_cone_cocycle':True,
            'ordinary_corner_obstruction_killed':True,'transgression_cocycle':True,
            'derivation_choice_cone_boundary':True,'gauge_choice_cone_boundary':True,
            'reconstructed_cokernel_projection':True},
        'transgression_cokernel_coordinates':asjson(cq),
        'cochain_sha256':{name:digest_vector(A) for name,A in [('ordinary_obstruction',O),('enhancement',QQ),('transgression',q),('gauge_boundary_first',X),('gauge_boundary_second',Y)]}
    }

if __name__=='__main__':
    actual=compute()
    if '--dump' not in sys.argv:
        expected=json.loads(HERE.joinpath('obstruction_transgression_v40_certificate.json').read_text())
        require(actual==expected,'complete frozen certificate')
    print(json.dumps(actual,indent=2,sort_keys=True))
