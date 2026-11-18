#!/usr/bin/env python3
"""Independent full-cochain solvability audit of second-order symmetry lifts.

Uses the displayed cocycles and first derivation lifts as inputs, checks them
again, then solves the simultaneous associativity/derivation condition without
quotient coordinates or any prechosen second-order associativity corrections.
"""
from pathlib import Path
import sys,json,time
CODE=Path(__file__).resolve().parent
if not (CODE/'audit_hh1_action_v36.py').is_file():
    CODE=CODE.parent/'output/vk_lo_deformations_v36/code'
sys.path.insert(0,str(CODE))
from audit_hh1_action_v36 import *
from itertools import combinations,product

def matrix(A):return fmpq_mat([[fmpq(c) for c in row] for row in A])
def selected(M,c):return fmpq_mat([[M[i,c]]for i in range(M.nrows())])
def data(n,V,col):
    D={}
    for i,(ch,ins,out) in enumerate(cochains(n)):
        if V[i,col]:D[ch,ins,out]=V[i,col]
    return D
def evaluate(D,ch,ins,out):return D.get((ch,ins,out),fmpq(0))
def quadratic_rhs(U,E,i,j):
    """Coefficient of t_i*t_j, evaluated directly on every basis tuple."""
    n2=len(cochains(2));n3=len(cochains(3));ans=fmpq_mat(n3+n2,1)
    Ui=data(2,U,i);Uj=data(2,U,j);Ei=data(1,E,i);Ej=data(1,E,j)
    choices=[(Ui,Uj,Ei)] if i==j else [(Ui,Uj,Ei),(Uj,Ui,Ej)]
    for row,(ch,ins,out) in enumerate(cochains(3)):
        a,b,c=ins;v=fmpq(0)
        for F,G,_ in choices:
            for mid in basis(ch[2]-ch[0]):v+=evaluate(G,ch[:3],(a,b),mid)*evaluate(F,(ch[0],ch[2],ch[3]),(mid,c),out)
            for mid in basis(ch[3]-ch[1]):v-=evaluate(G,ch[1:],(b,c),mid)*evaluate(F,(ch[0],ch[1],ch[3]),(a,mid),out)
        ans[row,0]=v
    # RHS for L_delta(v)-d1(theta)=-L_eta(u).
    for row,(ch,ins,out) in enumerate(cochains(2)):
        a,b=ins;v=fmpq(0)
        actions=[(Ei,Ui)] if i==j else [(Ei,Uj),(Ej,Ui)]
        for D,F in actions:
            for mid in basis(ch[2]-ch[0]):v-=evaluate(F,ch,(a,b),mid)*evaluate(D,(ch[0],ch[2]),(mid,),out)
            for mid in basis(ch[1]-ch[0]):v+=evaluate(D,ch[:2],(a,),mid)*evaluate(F,ch,(mid,b),out)
            for mid in basis(ch[2]-ch[1]):v+=evaluate(D,ch[1:],(b,),mid)*evaluate(F,ch,(a,mid),out)
        ans[n3+row,0]=v
    return ans

def audit(c):
    j=c['j'];mono,_=make_product(j,3-2*j,Q(0),Q(1));d1,_=differential(1,mono);d2,_=differential(2,mono)
    U=matrix(c['first_order_cocycles']);E=matrix(c['first_order_derivation_lifts'])
    require(d2*U==fmpq_mat(d2.nrows(),U.ncols()),'input cocycles')
    delta=delta_factory(j);LU=cochain_action_on_columns(2,delta,U)
    require(d1*E==LU,'input first-order derivation lifts')
    ident=fmpq_mat(d2.ncols(),d2.ncols())
    for z in range(ident.nrows()):ident[z,z]=1
    L=cochain_action_on_columns(2,delta,ident)
    M=fmpq_mat(d2.nrows()+d1.nrows(),d2.ncols()+d1.ncols())
    for i in range(d2.nrows()):
        for z in range(d2.ncols()):M[i,z]=d2[i,z]
    for i in range(d1.nrows()):
        for z in range(d2.ncols()):M[d2.nrows()+i,z]=L[i,z]
        for z in range(d1.ncols()):M[d2.nrows()+i,d2.ncols()+z]=-d1[i,z]
    R,rank=M.transpose().rref();piv=[next(z for z in range(R.ncols())if R[i,z])for i in range(rank)];free=[z for z in range(M.nrows())if z not in set(piv)]
    results=[];residues=[]
    for i,z in c['pairs']:
        b=quadratic_rhs(U,E,i,z)
        rem=[b[f,0]-sum(R[t,f]*b[p,0]for t,p in enumerate(piv))for f in free]
        nonzero=any(rem);results.append({'pair':[i,z],'solvable':not nonzero});residues.append(rem)
    Obs=fmpq_mat([[residues[z][i]for z in range(len(residues))]for i in range(len(free))])
    require(Obs.rank()==j,'independent quadratic rank')
    expected_unsolved=[]if j==0 else [[5,5]]
    require([x['pair']for x in results if not x['solvable']]==expected_unsolved,'independent square support')
    return {'j':j,'simultaneous_matrix_dimensions':[M.nrows(),M.ncols()],'simultaneous_rank':rank,'obstruction_rank':Obs.rank(),'pair_solvability':results,'checks':'Direct basis evaluation and full 2556-by-2204 block-matrix cokernel; no second-order correction chosen and no HH quotient-coordinate calculation used.'}

if __name__=='__main__':
    d=json.loads(Path(__file__).with_name('vk_symmetry_v37_certificate.json').read_text())
    print(json.dumps({'status':'PASS','arithmetic':'QQ','cases':[audit(c)for c in d['cases']]},indent=2))
