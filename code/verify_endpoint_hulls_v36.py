#!/usr/bin/env python3
"""Exact audit of even-weight endpoint Poisson smoothness and quantum HH1.

The all-m proof is harmonic decomposition plus a unit Schur residual; finite
ranks below only audit that proof. Default mode never writes its certificate.
"""
from pathlib import Path
import argparse, importlib.util, json, hashlib
import sympy as s
from flint import fmpq_mat

x,y,z,gamma,kappa=s.symbols('x y z gamma kappa')
xyz=(x,y,z); E=s.Matrix(xyz)
q=x*z-y*y

def mons(d):
 return [x**a*y**b*z**(d-a-b) for a in range(d+1) for b in range(d-a+1)]
def grad(f):return s.Matrix([s.diff(f,t) for t in xyz])
def div(F):return sum(s.diff(F[i],xyz[i]) for i in range(3))
def vf(F,f):return sum(F[i]*s.diff(f,xyz[i]) for i in range(3))
def vec(f,bs):
 p=s.Poly(s.expand(f),xyz);return [p.coeff_monomial(t) for t in bs]
def mat(cols):return fmpq_mat([[str(v) for v in row] for row in zip(*cols)])
def sha_matrix(M):return hashlib.sha256(str(M).encode()).hexdigest()
def rank(cols):return mat(cols).rank()
def zero(f):
 if s.expand(f)!=0:raise AssertionError(s.expand(f))

def case(j):
 m=2*j;n=m+2;N=lambda a:(a+2)*(a+1)//2
 basis=mons(m+1);target=mons(m+2);targetM=mons(m+3)
 source=[]
 for i in range(3):
  for b in basis:
   F=s.zeros(3,1);F[i]=b;source.append(F)
 beta=s.Rational(m+3,2)
 L=lambda F:beta*vf(F,q)-q*div(F)
 cols=[vec(L(F),target) for F in source]
 LM=mat(cols);lr=LM.rank();assert lr==N(m+2)-1
 cq=vec(q**(j+1),target)
 assert rank(cols+[cq])==lr+1
 # Actual Hamiltonian kernel plus Euler subspace exhaust the raw kernel.
 kernels=[grad(q).cross(grad(H)) for H in basis]
 eulers=[g*E for g in mons(m)]
 combined=kernels+eulers
 Fbasis=lambda F:[v for a in F for v in vec(a,basis)]
 kr=rank([Fbasis(F) for F in combined]);assert kr==N(m+1)+N(m)
 for F in combined:zero(L(F))
 assert len(source)-lr==kr
 H0=q**j*y;FH=grad(q).cross(grad(H0))
 F0=q**j*s.Matrix([0,y/2,z])
 for v in FH-2*F0+q**j*E:zero(v)
 K=lambda F:q*F[0]-x*vf(F,q)/2
 zero(K(FH)+x*q**(j+1))
 Mcols=[vec(x*L(F),targetM) for F in source]
 assert rank(Mcols+[vec(K(FH),targetM)])==lr+1
 ham=[grad(q).cross(grad(x*g)) for g in mons(m)]
 hamrank=rank([Fbasis(F) for F in ham]);assert hamrank==N(m)
 assert rank([Fbasis(F) for F in ham+[FH]])==N(m)+1
 # Full first derivative D(c)=0 and M(c,D;F)=0, retaining Euler kernel.
 c=x*q;a0=-s.Rational(m+3,2*m);D=a0*s.Matrix([0,x,2*y])
 mixed=lambda c,D,F:s.Rational(m+3,3)*vf(F,c)-s.Rational(m,3)*E.cross(D).dot(F)-c*div(F)
 zero(mixed(c,D,F0))
 dvars=[]
 for c1 in mons(3):dvars.append((c1,s.zeros(3,1),s.zeros(3,1)))
 for i in range(3):
  for l in range(3):
   if i==l:continue
   D1=s.zeros(3,1);D1[i]=xyz[l];dvars.append((0,D1,s.zeros(3,1)))
 dvars.extend([(0,s.Matrix([x,0,-z]),s.zeros(3,1)),(0,s.Matrix([0,y,-z]),s.zeros(3,1))])
 dvars.extend((0,s.zeros(3,1),F) for F in source)
 jac=[]
 for c1,D1,F1 in dvars:
  base=vf(D,c1)+vf(D1,c)
  mix=mixed(c1,D1,F0)+mixed(c,D,F1)
  jac.append(vec(base,mons(3))+vec(mix,targetM))
 J=mat(jac);jr=J.rank()
 tangent=len(dvars)-jr-N(m);assert tangent==N(m+1)+8
 return {'m':m,'j':j,'r':0,'raw_mixed_source_dimension':len(source),
  'mixed_target_after_dividing_x':len(target),'mixed_rank_QQ':lr,
  'Euler_dimension':N(m),'mixed_kernel_on_Euler_quotient':N(m+1),
  'mixed_cokernel_after_dividing_x':1,'Casimir_power_increases_rank':True,
  'kappa_derivative_increases_rank':True,'Hamiltonian_and_Euler_kernel_exhaustion':True,
  'w_translation_rank':hamrank,'w_scaling_adds_independent_direction':True,
  'full_Jacobian_raw_columns':len(dvars),'full_Jacobian_rows':len(mons(3))+len(targetM),
  'full_Jacobian_rank_QQ':jr,'full_Poisson_tangent_dimension':tangent,
  'L_matrix_sha256':sha_matrix(LM),'full_Jacobian_sha256':sha_matrix(J)}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--write-certificate',action='store_true');args=parser.parse_args()
 # Symbolic all-integer identities, not sampled degree identities.
 n,e,ell=s.symbols('n e ell',integer=True,nonnegative=True)
 zero((n*(n+1)-2*e*(2*(n-2*e)+2*e+1))-(n-2*e)*(n-2*e+1))
 j0=s.symbols('j0',integer=True,nonnegative=True)
 zero((2*j0+3)*2*(j0+1)-2*(j0+1)*(2*(j0+1)+1))
 m=s.symbols('m',integer=True,positive=True);a=s.symbols('a')
 qg=q+gamma*z*z;cg=x*qg;Dg=a*s.Matrix([0,x+2*gamma*z,2*y])
 fs=s.Matrix([s.Function('F'+str(i))(*xyz) for i in range(3)])
 mixed=(m+3)*vf(fs,cg)/3-m*E.cross(Dg).dot(fs)/3-cg*div(fs)
 kk=(m+3+2*m*a)/3
 expected=x*((m+3)*vf(fs,qg)/2-qg*div(fs))+kk*(qg*fs[0]-x*vf(fs,qg)/2)
 zero(mixed-expected)
 # Integer rank checks. All arithmetic is exact QQ.
 cases=[case(j) for j in [2,3,4,5]]
 # Reuse the frozen prior CGG multiplication evaluator, not its hull claim.
 here=Path(__file__).resolve();prior=here.parent/'verify_fixed_hulls_derivations_v35.py'
 if not prior.exists():prior=here.parent.parent/'output/vk_lo_deformations_v35/code/verify_fixed_hulls_derivations_v35.py'
 spec=importlib.util.spec_from_file_location('fixed_hulls_v35',prior)
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 quantum=[]
 for j in [2,3,4]:
  r=mod.case(j,0);r.pop('expected_hull_length_from_structural_theorem',None)
  quantum.append(r)
 out={'status':'PASS','version':36,'coefficient_field':'QQ',
  'scope':'All-m identities plus finite exact matrix audits of the endpoint proof; no extrapolation from finite m.',
  'symbolic_mixed_decomposition':True,'symbolic_harmonic_eigenvalue':True,
  'symbolic_Fischer_annihilator':True,'poisson_cases':cases,
  'quantum_HH1_cases':quantum,'prior_multiplication_evaluator_sha256':hashlib.sha256(prior.read_bytes()).hexdigest()}
 text=json.dumps(out,ensure_ascii=False,indent=2)+'\n'
 cert=here.with_name('endpoint_hulls_v36_certificate.json')
 if args.write_certificate:cert.write_text(text)
 else:assert out==json.loads(cert.read_text()),'recomputed certificate differs'
 print(text,end='')
if __name__=='__main__':main()
