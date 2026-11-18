#!/usr/bin/env python3
"""Exact QQ audits of pullback Ore Beilinson algebras and Poisson stabilizers.

Structural theorem: for the stated nonresonant pullback points with nonzero
residual mixed term, HH1=2 and the fixed hull is
C[[t1,t2,a,b]]/(a^(m+2),ab,b^2). These finite audits supplement, but do not
replace, the all-weight orbit and formal-transfer arguments.
No output certificate is overwritten in normal verification mode.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import comb,factorial
from pathlib import Path
import argparse,importlib.util,json

BASE=Path(__file__).with_name('verify_fixed_hulls_derivations_v35.py')
if not BASE.exists():
 BASE=Path(__file__).resolve().parents[1]/'output/vk_lo_deformations_v36/code/verify_fixed_hulls_derivations_v35.py'
spec=importlib.util.spec_from_file_location('old_derivations',BASE)
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
ZERO,UNIT,GEN=base.ZERO,base.UNIT,base.GEN
canonical,add,scale,mul,monomial=base.canonical,base.add,base.scale,base.mul,base.monomial
weighted_basis,rank_qq=base.weighted_basis,base.rank_qq

def derivative(p,i):
 out={}
 for e,c in p:
  if e[i]:
   f=list(e);f[i]-=1;out[tuple(f)]=c*e[i]
 return canonical(out)

class Ore:
 def __init__(self,m,A=2,B=5,u=1,s=1):
  self.m,self.A,self.B,self.u,self.s=m,F(A),F(B),F(u),F(s)
  t=F(m,3*(m+3));A,B=self.A,self.B
  self.images=(canonical({(2,0,0,0):F(1,3)+t*A,(1,1,0,0):F(2,3)+t*B}),
   canonical({(1,1,0,0):-F(2,3)+t*A,(0,2,0,0):-F(1,3)+t*B}),
   ZERO,canonical({(m+1,0,0,0):self.u,(1,0,0,1):-F(m,m+3)*A,(0,1,0,1):-F(m,m+3)*B}))
 @lru_cache(None)
 def delta(self,p):return add(*(mul(derivative(p,i),self.images[i]) for i in (0,1,3)))
 @lru_cache(None)
 def star(self,p,q):
  ans=ZERO;n=0;dq=q;dp=p
  while dp:
   ans=add(ans,scale(self.s**n/F(factorial(n)),mul(dp,dq)))
   n+=1;dp=derivative(dp,2);dq=self.delta(dq)
  return ans
 @lru_cache(None)
 def word(self,w):
  ans=UNIT
  for i in w:ans=self.star(ans,GEN[i])
  return ans
 def polywords(self,p):
  return {(0,)*e[0]+(1,)*e[1]+(3,)*e[3]+(2,)*e[2]:c for e,c in p}
 def relations(self):
  quad=[{(1,0):F(1),(0,1):F(-1)}]
  for i in (0,1):
   rel={(2,i):F(1),(i,2):F(-1)}
   for w,c in self.polywords(self.images[i]).items():rel[w]=rel.get(w,0)-self.s*c
   quad.append(rel)
  mixed=[{(3,0):F(1),(0,3):F(-1)},{(3,1):F(1),(1,3):F(-1)}]
  rel={(2,3):F(1),(3,2):F(-1)}
  for w,c in self.polywords(self.images[3]).items():rel[w]=rel.get(w,0)-self.s*c
  mixed.append(rel)
  assert all(not add(*(scale(c,self.word(w)) for w,c in rel.items())) for rel in quad+mixed)
  return quad,mixed

def quantum_case(m,A=2,B=5,u=1,s=1):
 alg=Ore(m,A,B,u,s);quad,mixed=alg.relations()
 variables=[(start,gen,GEN[target]) for start in range(m+2) for gen in range(3) for target in range(3)]
 variables += [(start,3,monomial(e)) for start in range(3) for e in weighted_basis(m,m)]
 choices={}
 for i,(start,gen,p) in enumerate(variables):choices.setdefault((start,gen),[]).append((i,p))
 rows=[];instances=0;parameter_columns=[[],[]]
 t=F(m,3*(m+3))
 parameter_images=[
  [scale(t,mul(GEN[0],GEN[0])),scale(t,mul(GEN[0],GEN[1])),scale(-3*t,mul(GEN[0],GEN[3]))],
  [scale(t,mul(GEN[0],GEN[1])),scale(t,mul(GEN[1],GEN[1])),scale(-3*t,mul(GEN[1],GEN[3]))]]
 for degree,relations in [(2,quad),(m+1,mixed)]:
  basis=weighted_basis(degree,m);index={e:i for i,e in enumerate(basis)}
  for start in range(m+3-degree):
   for relation_index,rel in enumerate(relations):
    block=[[F(0) for _ in variables] for _ in basis]
    for word,c in rel.items():
     pos=start
     for slot,gen in enumerate(word):
      pre,suf=alg.word(word[:slot]),alg.word(word[slot+1:])
      for col,p in choices[(pos,gen)]:
       for e,v in alg.star(alg.star(pre,p),suf):block[index[e]][col]+=c*v
      pos+=m if gen==3 else 1
    rows.extend(block);instances+=1
    image_index=(relation_index-1 if relation_index>0 else None) if degree==2 else (2 if relation_index==2 else None)
    for j in range(2):
     derivative_relation=dict(scale(-alg.s,parameter_images[j][image_index])) if image_index is not None else {}
     parameter_columns[j].extend(derivative_relation.get(e,F(0)) for e in basis)
 rank,pivots=rank_qq(rows)
 augmented_rank=rank_qq([row+[parameter_columns[j][i] for j in range(2)] for i,row in enumerate(rows)])[0]
 parameter_rank=augmented_rank-rank
 assert parameter_rank==(0 if F(s)==0 else 2)
 expected=comb(m+2,2)+9 if F(s)==0 else 2
 assert len(variables)-rank==expected+m+2
 vectors=[]
 for vertex in range(1,m+3):
  v=[]
  for start,gen,p in variables:
   end=start+(m if gen==3 else 1)
   v.append(F(int(end==vertex)-int(start==vertex)) if p==GEN[gen] else F(0))
  assert all(sum(a*b for a,b in zip(row,v))==0 for row in rows);vectors.append(v)
 for target in (0,1):
  v=[F(gen==2 and p==GEN[target]) for start,gen,p in variables]
  assert all(sum(a*b for a,b in zip(row,v))==0 for row in rows);vectors.append(v)
 assert rank_qq(list(map(list,zip(*vectors))))[0]==m+4
 digest=sha256('\n'.join(','.join(map(str,row)) for row in rows).encode()).hexdigest()
 return {'m':m,'A':str(F(A)),'B':str(F(B)),'u':str(F(u)),'s':str(F(s)),
  'variables':len(variables),'equations':len(rows),'relation_instances':instances,
  'rank_QQ':rank,'Der_E_dimension':len(variables)-rank,'inner_dimension':m+2,'HH1':expected,
  'z_to_x_and_z_to_y_verified_outer':True,'AB_Kodaira_Spencer_rank_mod_gauge':parameter_rank,'AB_relation_derivative_sha256':sha256('\n'.join(','.join(map(str,col)) for col in parameter_columns).encode()).hexdigest(),'all_relations_vanish':True,'matrix_sha256':digest,'pivot_columns':pivots}

def poisson_case(m):
 import sympy as sp
 x,y,z,w=xs=sp.symbols('x y z w')
 c=x*y*(x+y);L=2*x+5*y
 d=(sp.diff(c,y)/3+sp.Rational(m,3*(m+3))*x*L,
    -sp.diff(c,x)/3+sp.Rational(m,3*(m+3))*y*L,0,
    x**(m+1)-sp.Rational(m,m+3)*L*w)
 P=sp.zeros(4)
 for i in (0,1,3):P[2,i]=d[i];P[i,2]=-d[i]
 fields=[]
 for i in range(3):
  for j in range(3):
   if i==j:continue
   v=[0]*4;v[i]=xs[j];fields.append(v)
 fields += [[x,0,-z,0],[0,y,-z,0],[0,0,0,w]]
 for a in range(m+1):
  for b in range(m-a+1):fields.append([0,0,0,x**a*y**b*z**(m-a-b)])
 cols=[]
 for Y in fields:
  out={}
  for i in range(4):
   for j in range(i+1,4):
    v=sp.expand(sum(Y[k]*sp.diff(P[i,j],xs[k])-P[k,j]*sp.diff(Y[i],xs[k])-P[i,k]*sp.diff(Y[j],xs[k]) for k in range(4)))
    for e,c0 in sp.Poly(v,*xs).terms():
     if c0:out[(i,j,e)]=F(int(c0.p),int(c0.q))
  cols.append(out)
 keys=sorted(set().union(*(set(c) for c in cols)))
 rows=[[c.get(k,F(0)) for c in cols] for k in keys]
 rank,pivots=rank_qq(rows)
 assert len(fields)==comb(m+2,2)+9 and rank==len(fields)-2
 for Y in ([0,0,x,0],[0,0,y,0]):assert not cols[fields.index(Y)]
 return {'m':m,'Lie_aut_dimension':len(fields),'orbit_rank_QQ':rank,'stabilizer_dimension':2,
 'kernel_contains_x_dz_y_dz':True,'matrix_sha256':sha256('\n'.join(','.join(map(str,r)) for r in rows).encode()).hexdigest(),'pivot_columns':pivots}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--candidate',action='store_true');args=parser.parse_args()
 quantum=[quantum_case(3,s=0)]+[quantum_case(m) for m in (3,4,5,6)]+[quantum_case(3,A=3,B=7,u=2,s=F(-1,2))]
 poisson=[poisson_case(m) for m in (3,4,5,6)]
 result={'version':37,'status':'PASS','arithmetic':'QQ','quantum_cases':quantum,'poisson_cases':poisson,
 'scope':'Finite verification of derivation ranks and stabilizer ranks. The all-m full-hull theorem is structural, not extrapolated from these samples.'}
 cert=Path(__file__).with_name('pullback_fixed_hull_v37_certificate.json')
 if not args.candidate:assert result==json.loads(cert.read_text())
 print(json.dumps(result,ensure_ascii=False,indent=2))
if __name__=='__main__':main()
