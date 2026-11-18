"""Necessary quadratic flatness equations from v21's exact first-neighbourhood model.

No recomputation of determinant jets; all arithmetic is exact over Q. If the
cyclic-torsion splitting M=A^4 + A/J_M holds, M tensor A/J_M is free of rank5,
so the quadratic commuting-matrix obstruction of its first-order fibre
operators must vanish on A/J_M. The three known linear equations are removed
allowing their nonlinear lifts, via three transverse first-order defects.
"""
import argparse,json,hashlib,sys
if not __debug__:
    raise RuntimeError("Do not use -O: assertions are part of the verification.")
from pathlib import Path
from itertools import combinations_with_replacement
from flint import fmpq_mat
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'archive/v21/code/relative_first_neighbourhood_v21_certificate.json'
cert=json.loads(SOURCE.read_text())
BASE=cert['base_indices_zero_based']
N=5
zero=lambda: fmpq_mat(N,N)
A={n:{int(k) if k else -1:fmpq_mat(v['entries']) for k,v in data.items()} for n,data in cert['canonical_actions'].items()}
names=['s','u','v']; pairs=[(0,1),(0,2),(1,2)]
C=[A[n][-1] for n in names]
comm=lambda X,Y:X*Y-Y*X
flat=lambda mats:[m[i,j] for m in mats for i in range(N) for j in range(N)]
# t8=-9t9+4t10-5t14; t11=t14; t13=t14.
FREE=[i for i in BASE if i not in [7,10,12]]
sub={i:{i:1} for i in FREE}
sub[8][7]=-9;sub[9][7]=4;sub[13].update({7:-5,10:1,12:1})
L=[]
for z in FREE:
 row=[]
 for name in names:
  mat=zero()
  for i,c in sub[z].items(): mat+=A[name][i]*c
  row.append(mat)
 L.append(row)
assert all(not any(flat([comm(L[z][a],C[b])+comm(C[a],L[z][b]) for a,b in pairs])) for z in range(10))
# Linearized conjugacy-invariant commuting equations, 75 by75.
cols=[]
for k in range(3):
 for i in range(N):
  for j in range(N):
   X=[zero() for _ in range(3)];X[k][i,j]=1
   cols.append(flat([comm(X[a],C[b])+comm(C[a],X[b]) for a,b in pairs]))
D=fmpq_mat(cols).transpose()
# Unknown quadratic lifts of the three known linear equations can create
# exactly these transverse defects. Their inclusion makes the result intrinsic
# modulo the eliminated nonlinear regular sequence.
trans=[]
for z in [7,10,12]:
 trans.append(flat([comm(A[names[a]][z],C[b])+comm(C[a],A[names[b]][z]) for a,b in pairs]))
DA=fmpq_mat(cols+trans).transpose()
# Quotient via left nullspace, computed by RREF of transpose.
rr,rk=DA.transpose().rref()
piv=[]
for i in range(rk):
 piv.append(next(j for j in range(75) if rr[i,j]))
free=[j for j in range(75) if j not in piv]
P=fmpq_mat(len(free),75)
for r,j in enumerate(free):
 P[r,j]=1
 for i,k in enumerate(piv):P[r,k]=-rr[i,j]
assert not any(P*DA)
mons=list(combinations_with_replacement(range(10),2))
ob=[]
for i,j in mons:
 blocks=[]
 for a,b in pairs:
  z=comm(L[i][a],L[j][b])
  if i!=j:z+=comm(L[j][a],L[i][b])
  blocks.append(z)
 ob.append(flat(blocks))
O=P*fmpq_mat(ob).transpose()
RR,rank=O.rref()
polys=[]
for i in range(rank):
 polys.append({','.join(str(FREE[z]+1) for z in m):str(RR[i,j]) for j,m in enumerate(mons) if RR[i,j]})
report={'status':'PASS','source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
 'coordinates_one_based':[i+1 for i in FREE],
 'eliminated_linear_coordinates_one_based':[8,11,13],
 'linear_commutator_rank':D.rank(),'augmented_rank':DA.rank(),
 'quadratic_obstruction_rank_mod_transverse_defects':rank,
 'quadratic_polynomials':polys,
 'scope':'Necessary homogeneous quadratic equations in gr(A/J_M), after eliminating the three known linear equations. This does not compute all quadratic relations or beta.'}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--write-certificate',action='store_true')
args=parser.parse_args()
target=HERE/'second_order_module_obstructions.json'
if args.write_certificate:
    target.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
else:
    assert json.loads(target.read_text())==report, 'Stored exploratory certificate differs.'
print(json.dumps(report,indent=2))
