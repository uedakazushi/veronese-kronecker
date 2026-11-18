#!/usr/bin/env python3
"""Exact full-cocycle/full-cochain image-rank audit of every Jordan block.

No quotient coordinates, no imported root-derived matrices or rank lists.
"""
from audit_hh1_action_v36 import *

BLOCKS={0:{2:[13,10,7,5],3:[14,11,8,5,1]},1:{2:[11,9,6,5,3,1],3:[13,10,7,5,3,1]}}

def ident(n):
    M=fmpq_mat(n,n)
    for i in range(n):M[i,i]=1
    return M

def expected_ranks(blocks):return [sum(max(b-k,0) for b in blocks) for k in range(max(blocks)+1)]

def audit_case(j):
    start=time.time();mono,_=make_product(j,3-2*j,Q(0),Q(1));delta=delta_factory(j)
    d1,_=differential(1,mono);d2,_=differential(2,mono)
    K,r2=nullspace(d2);r1=d1.rank();require((r1,r2)==(616,933),'differentials')
    rows={};joint={}
    for n,A,base in [(2,K,d1),(3,ident(d2.nrows()),d2)]:
        brank=base.rank();expected=expected_ranks(BLOCKS[j][n]);computed=[A.ncols()-brank];jranks=[A.ncols()]
        for k in range(1,len(expected)):
            A=cochain_action_on_columns(n,delta,A)
            if n==2:require(d2*A==fmpq_mat(d2.nrows(),A.ncols()),'cocycles preserved')
            joint_rank=hjoin(base,A).rank();computed.append(joint_rank-brank);jranks.append(joint_rank)
            print('audit',j,n,k,computed[-1],round(time.time()-start,2),file=sys.stderr,flush=True)
        require(computed==expected,'full rank sequence')
        rows[str(n)]={'ranks':computed,'blocks':BLOCKS[j][n]};joint[str(n)]=jranks
    return {'j':j,'r':3-2*j,'HH_actions':rows,'augmented_matrix_ranks':joint,'boundary_ranks':{'2':r1,'3':r2},
      'algorithm':'rank([d_(n-1),L_delta^k K_n])-rank d_(n-1); K_2=full ker d2, K_3=identity C3'}

if __name__=='__main__':
    result={'status':'PASS','arithmetic':'Exact QQ, python-flint fmpq_mat',
      'scope':'Independent all-power audit via full cocycle and cochain spaces, without quotient-coordinate matrices.',
      'cases':[audit_case(j) for j in (0,1)]}
    print(json.dumps(result,indent=2,sort_keys=True))
