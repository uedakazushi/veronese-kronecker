#!/usr/bin/env python3
"""Exact ambient-completion tangent and intrinsic symmetry obstruction.

Normal execution is read-only. The explicit PBW Ore algebra over Q[gamma]/gamma^2
is identified with the fixed j=r=1 CGG standard algebra at gamma=0. Every
nonidentity input triple on all six objects is checked. Its corner tangent,
independent derivation/associativity lifts, and secondary cokernel class are
computed over Q and compared with the frozen certificate.
--dump prints the complete newly computed certificate to stdout without writing.
"""
from pathlib import Path
import sys,json,time,hashlib
sys.dont_write_bytecode=True
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations,product
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BASE=HERE if (HERE/'verify_vk_symmetry_jump_v37.py').is_file() else ROOT/'output/vk_lo_deformations_v37/code'
sys.path.insert(0,str(BASE))
from verify_vk_symmetry_jump_v37 import *
# Coefficients are pairs over Q[gamma]/gamma^2.
def ca(a,b):return(a[0]+b[0],a[1]+b[1])
def cm(a,b):return(a[0]*b[0],a[0]*b[1]+a[1]*b[0])
def cs(a,b):return(a[0]*b,a[1]*b)
def put(p,m,c):
 if not any(c):return
 p[m]=ca(p.get(m,(Q(0),Q(0))),c)
 if not any(p[m]):del p[m]
def pa(p,q,c=Q(1)):
 o=p.copy()
 for m,v in q.items():put(o,m,cs(v,c))
 return o
def mon(w):return {tuple(w):(Q(1),Q(0))}
def pc(p,c):return {w:cs(v,c) for w,v in p.items() if c}
R={(1,0):{(0,1):(Q(1),Q(2)),(0,0):(Q(-1),Q(-1)),(0,2):(Q(0),Q(-2))},
 (2,0):{(0,2):(Q(1),Q(2)),(0,1):(Q(-2),Q(-2)),(0,0):(Q(1),Q(1))},
 (2,1):{(1,2):(Q(1),Q(0)),(0,1):(Q(1),Q(1)),(0,2):(Q(-1),Q(-1))}}
@lru_cache(None)
def nf(w):
 for i in range(len(w)-1):
  if (w[i],w[i+1]) in R:
   p={}
   for v,c in R[w[i],w[i+1]].items():
    for z,d in nf(w[:i]+v+w[i+2:]).items():put(p,z,cm(c,d))
   return p
 return {w:(Q(1),Q(0))}
def pm(p,q):
 o={}
 for u,c in p.items():
  for v,d in q.items():
   for w,e in nf(u+v).items():put(o,w,cm(cm(c,d),e))
 return o
def comm(p,q):return pa(pm(p,q),pm(q,p),-1)
def substitute(p,imgs):
 ans={}
 for w,c in p.items():
  tmp={():c}
  for a in w:tmp=pm(tmp,imgs[a])
  ans=pa(ans,tmp)
 return ans
x,y,Z=(mon([i]) for i in range(3))
Q0=pa(pa(mon([0,2]),mon([0,1]),-1),mon([1,1]),-1)
G0={(0,1,2):(Q(1),Q(0)),(0,1,1):(Q(-1),Q(0)),(0,0,2):(Q(-1),Q(0)),(0,0,1):(Q(1),Q(0)),(1,1,1):(Q(-2,3),Q(0))}
H0={w:(v[0],Q(0)) for w,v in pm(Q0,G0).items() if v[0]}
H1={(1,1,1,1,1):Q(-8,3),(1,1,1,2,2):Q(-5,3),(0,1,2,2,2):Q(5,2),(0,1,1,2,2):Q(5,2),(0,1,1,1,2):Q(-5)}
H=pa(H0,{w:(Q(0),v) for w,v in H1.items()})
sigma=[x,{(1,):(Q(1),Q(2)),(0,):(Q(-1),Q(-1)),(2,):(Q(0),Q(-2))},
 {(2,):(Q(1),Q(2)),(1,):(Q(-2),Q(-2)),(0,):(Q(1),Q(1))}]
sigma2=[substitute(a,sigma) for a in sigma]
deltas=[]
for u in [x,y,Z]:
 c=comm(u,H)
 require(all(w[:2]==(0,0) for w in c),'H commutator not divisible by x^2')
 deltas.append({w[2:]:c0 for w,c0 in c.items()})
for i in range(3):R[3,i]=pa({w+(3,):v for w,v in sigma2[i].items()},deltas[i])
nf.cache_clear()

def word(u):return sum(((i,)*n for i,n in enumerate(u)),())
def exps(w):return tuple(w.count(i) for i in range(4))
mono_minus,mul_minus=make_product(1,1,Q(-1),Q(1))
mono_zero,mul_zero=make_product(1,1,Q(0),Q(1))
gens=[{tuple(int(i==j) for i in range(4)):Q(1)} for j in range(4)]
gens[2][(0,1,0,0)]=Q(1)
@lru_cache(None)
def E(deg):
 b=basis(deg);lookup={u:i for i,u in enumerate(b)}
 A=zero(len(b),len(b))
 for col,u in enumerate(b):
  p={(0,0,0,0):Q(1)}
  for v in word(u):p=mul_minus(p,gens[v])
  for v,c in p.items():A[lookup[v],col]=fmpq(c.numerator,c.denominator)
 return A,A.inv()
# T=1+N; powers use the finite ordinary-binomial expression.
fields=[{}, {(1,0,0,0):Q(1)}, {(0,1,0,0):Q(2)}, {(1,0,2,0):Q(-1),(0,2,1,0):Q(1)}]
def N(p):
 ans={}
 for u,c in p.items():
  for i,v in enumerate(u):
   if not v:continue
   z=list(u);z[i]-=1
   for w,e in fields[i].items():add(ans,plus(tuple(z),w),c*v*e)
 return ans
@lru_cache(None)
def tp(u,n):
 out={};p={u:Q(1)};choose=Q(1);k=0
 while p:
  for v,c in p.items():add(out,v,choose*c)
  k+=1;choose*=Q(n-k+1,k);p=N(p)
 return out
@lru_cache(None)
def Tmat(deg,n):
 b=basis(deg);idx={u:i for i,u in enumerate(b)};A=zero(len(b),len(b))
 for k,u in enumerate(b):
  for v,c in tp(u,n).items():A[idx[v],k]=fmpq(c.numerator,c.denominator)
 return A
@lru_cache(None)
def inmat(i,j):return E(j-i)[1]*Tmat(j-i,-j)
@lru_cache(None)
def outmat(i,j):return Tmat(j-i,j)*E(j-i)[0]
@lru_cache(None)
def family(i,j,k,a,b):
 ba=basis(j-i);bb=basis(k-j);bc=basis(k-i)
 ia=ba.index(a);ib=bb.index(b)
 A=inmat(i,j);B=inmat(j,k)
 pa0={word(u):(Q(str(A[l,ia])),Q(0)) for l,u in enumerate(ba) if A[l,ia]}
 pb0={word(u):(Q(str(B[l,ib])),Q(0)) for l,u in enumerate(bb) if B[l,ib]}
 r=pm(pa0,pb0);V=zero(len(bc),2);idx={u:l for l,u in enumerate(bc)}
 for w,c in r.items():
  for n in range(2):V[idx[exps(w)],n]=fmpq(c[n].numerator,c[n].denominator)
 W=outmat(i,k)*V
 return tuple({u:Q(str(W[l,n])) for l,u in enumerate(bc) if W[l,n]} for n in range(2))
def vector_tangent():
 U=zero(len(cochains(2)),1)
 for l,(chain,ins,out) in enumerate(cochains(2)):
  i,j,k=chain;a,b=ins
  U[l,0]=fmpq(str(family(i,j,k,a,b)[1].get(out,Q(0))))
 return U

BASE_RULES=R
BASE_GENERATORS=[x,y,Z]
def divisibility_search_ranks(P,deg):
 bs=[word(u) for u in basis(deg) if u[3]==0]
 outs=[word(u) for u in basis(deg+1) if u[3]==0 and u[0]<2]
 rows=[];rhs=[]
 for uu in BASE_GENERATORS:
  c=comm(uu,P)
  for w in outs:
   require(not c.get(w,(Q(0),Q(0)))[0],'zeroth divisibility in search')
   rows.append([fmpq(str(comm(uu,mon(b)).get(w,(Q(0),Q(0)))[0])) for b in bs])
   rhs.append(fmpq(str(-c.get(w,(Q(0),Q(0)))[1])))
 M=fmpq_mat(rows);Aug=fmpq_mat([row+[v] for row,v in zip(rows,rhs)])
 return {'shape':[len(rows),len(bs)],'rank':M.rank(),'augmented_rank':Aug.rank()}
def compute():
 start=time.time();print('build tangent',file=sys.stderr,flush=True)
 expected_v37_sha='5be59503cba19747b0e6665406d58c45e7c2a9a8e9b7283ef192248ee27bd85c'
 frozen_v37=(BASE/'vk_symmetry_v37_certificate.json').read_bytes()
 require(hashlib.sha256(frozen_v37).hexdigest()==expected_v37_sha,'v37 certificate checksum')
 require(pm(BASE_RULES[2,1],BASE_GENERATORS[0])==pm(BASE_GENERATORS[2],BASE_RULES[1,0]),'base Diamond overlap')
 for aa,bb in [(1,0),(2,0),(2,1)]:
  require(substitute(mon([aa,bb]),sigma)==substitute(BASE_RULES[aa,bb],sigma),'sigma relation')
 for ii,uu in enumerate(BASE_GENERATORS):
  require(pm(uu,BASE_GENERATORS[0])==pm(BASE_GENERATORS[0],sigma[ii]),'normality')
 searchH=divisibility_search_ranks(H0,5);searchG=divisibility_search_ranks(G0,3)
 require(searchH=={'shape':[39,21],'rank':10,'augmented_rank':10},'H search ranks')
 require(searchG=={'shape':[27,10],'rank':6,'augmented_rank':7},'G search ranks')
 # All degree <=5 PBW multiplication checks special fibre against the original CGG finite algebra.
 paircount=0
 for i,j,k in combinations(range(6),3):
  for a,b in product(basis(j-i),basis(k-j)):
   require(family(i,j,k,a,b)[0]==mono_zero(a,b),'special fibre mismatch')
   paircount+=1
 print('special fibre verified',paircount,time.time()-start,file=sys.stderr,flush=True)
 # First-order associativity on every nonidentity full-algebra triple.
 triplecount=0
 def fm(i,j,k,p,q):
  out=[{},{}]
  for n,pp in enumerate(p):
   for m,qq in enumerate(q):
    if n+m>1:continue
    for a,c in pp.items():
     for b,d in qq.items():
      val=family(i,j,k,a,b)
      for l in range(2-n-m):
       for z,e in val[l].items():add(out[n+m+l],z,c*d*e)
  return out
 for i,j,k,l in combinations(range(6),4):
  for a,b,c in product(basis(j-i),basis(k-j),basis(l-k)):
   lhs=fm(i,k,l,family(i,j,k,a,b),({c:Q(1)},{}))
   rhs=fm(i,j,l,({a:Q(1)},{}),family(j,k,l,b,c))
   require(lhs==rhs,'ambient first-order associativity')
   triplecount+=1
 print('associativity verified',triplecount,time.time()-start,file=sys.stderr,flush=True)
 d1,_=differential(1,mono_zero);d2,_=differential(2,mono_zero);U=vector_tangent()
 require(d2*U==zero(d2.nrows(),1),'tangent not cocycle')
 R,b=d1.transpose().rref();ps=pivots(R,b);fs=[i for i in range(d1.nrows()) if i not in set(ps)]
 df=select(d2,range(d2.nrows()),fs);Z,zr=df.rref();zp=pivots(Z,zr);zf=[i for i in range(len(fs)) if i not in set(zp)]
 V=zero(len(fs),len(zf))
 for k,c in enumerate(zf):
  V[c,k]=1
  for i,p in enumerate(zp):V[p,k]=-Z[i,c]
 Rfree=select(R,range(b),fs).transpose()
 def hclass(W):
  Wf=select(W,fs,range(W.ncols()))-Rfree*select(W,ps,range(W.ncols()))
  hh=select(Wf,zf,range(W.ncols()))
  require(Wf==V*hh,'not cocycle')
  return hh
 h=hclass(U)
 cert=json.loads(frozen_v37)
 case=next(c for c in cert['cases'] if c['j']==1)
 HH=fmpq_mat(case['HH2_matrix']);K=fmpq_mat(case['kernel_basis']);KC=fmpq_mat(case['kernel_to_cokernel_matrix'])
 require(h!=zero(35,1),'completion tangent trivial')
 require(HH*h==zero(35,1),'completion tangent not in K')
 KR,kr=K.transpose().rref();kp=pivots(KR,kr)
 coords=select(K,kp,range(6)).solve(select(h,kp,[0]))
 require(K*coords==h,'K-coordinates wrong')
 cok=KC*coords
 print('K coordinates',asjson(coords),'coker',asjson(cok),file=sys.stderr,flush=True)
 # Independent secondary calculation using the actual Ore cocycle, rather than
 # evaluating only the frozen quadratic map on its cohomology coordinates.
 L=action(2,derivation(1,1))
 Uall=zero(d1.nrows(),35)
 for ii,ff in enumerate(fs):
  for kk in range(35):Uall[ff,kk]=V[ii,kk]
 require(hclass(L*Uall)==HH,'independent HH2 action recomputation')
 D1R,rr=d1.rref();pc1=pivots(D1R,rr);B1=select(d1,ps,pc1)
 etasmall=B1.solve(select(L*U,ps,[0]));Eta=zero(d1.ncols(),1)
 for ii,cc in enumerate(pc1):Eta[cc,0]=etasmall[ii,0]
 require(d1*Eta==L*U,'first derivation lift')
 rhs=compose22(cochain_dict(2,U),cochain_dict(2,U))
 D2T,rr=d2.transpose().rref();pr=pivots(D2T,rr);cs2=[fs[z] for z in zp]
 B2=select(d2,pr,cs2);vsmall=B2.solve(select(rhs,pr,[0]));Second=zero(d2.ncols(),1)
 for ii,cc in enumerate(cs2):Second[cc,0]=vsmall[ii,0]
 require(d2*Second==rhs,'second associativity correction')
 secondary=L*Second+act12(cochain_dict(1,Eta),cochain_dict(2,U))
 oh=hclass(secondary);HR,hr=HH.transpose().rref();hp=pivots(HR,hr);hf=[ii for ii in range(35) if ii not in set(hp)]
 directq=select(oh,hf,[0])-select(HR,range(hr),hf).transpose()*select(oh,hp,[0])
 qM=fmpq_mat(case['quadratic_obstruction_matrix']);pairs=case['quadratic_pairs'] if 'quadratic_pairs' in case else case['pairs']
 vv=fmpq_mat([[coords[i,0]*coords[j,0]] for i,j in pairs]);qval=qM*vv
 require(directq==qval,'independent secondary calculation mismatch')
 require(qval!=zero(qval.nrows(),1),'secondary class vanished')
 out={'version':38,'status':'PASS','arithmetic':'Exact rational arithmetic over Q[gamma]/(gamma^2)','baseline_v37_certificate_sha256':expected_v37_sha,'H_linear_search':searchH,'overrestricted_G_linear_search':searchG,'base_Diamond_overlap':True,'normality_and_sigma_relations':True,'ambient_objects':list(range(6)), 'corner_objects':list(OBJECTS),'special_fibre_pairs':paircount,'ambient_associativity_triples':triplecount,'completion_tangent_cochain':asjson(U),'HH2_coordinates':asjson(h),'kernel_coordinates':asjson(coords),'cokernel_coordinates':asjson(cok),'symmetry_quadratic_obstruction':asjson(qval),'in_kernel':True,'in_image':cok==zero(cok.nrows(),1),'symmetry_secondary_zero':qval==zero(qval.nrows(),1),'derivation_first_correction':asjson(Eta),'associativity_second_correction':asjson(Second),'secondary_cohomology_coordinates':asjson(oh),'independent_secondary_calculation':True,'H0':[[list(w),str(v[0])] for w,v in sorted(H0.items())],'H1':[[list(w),str(v)] for w,v in sorted(H1.items())]}
 print('done',time.time()-start,file=sys.stderr,flush=True)
 return out
if __name__=='__main__':
 actual=compute()
 if '--dump' in sys.argv:
  print(json.dumps(actual,indent=2,sort_keys=True))
 else:
  frozen=json.loads((HERE/'vk_completion_symmetry_v38_certificate.json').read_text())
  require(actual==frozen,'frozen v38 certificate mismatch')
  print(json.dumps({k:actual[k] for k in ['version','status','arithmetic','ambient_associativity_triples','special_fibre_pairs','in_kernel','in_image','symmetry_secondary_zero','kernel_coordinates','cokernel_coordinates','symmetry_quadratic_obstruction','independent_secondary_calculation']},indent=2,sort_keys=True))
