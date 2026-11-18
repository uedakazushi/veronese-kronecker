"""Independent polynomial audit via Groebner normal forms, not stored matrices."""
from pathlib import Path
if not __debug__:
    raise RuntimeError('Do not use -O: assertions are part of the certificates.')
import argparse,hashlib,json
import sympy as s
HERE=Path(__file__).resolve().parent
u,v,w,z,X,Y=s.symbols('u v w z X Y')
G=s.groebner([X*Y-u,Y**2-2*X**2-v-w*X-z*Y],Y,X,order='grevlex',domain=s.QQ[u,v,w,z])
basis=[1,X,Y,X**2]
def coords(f):
    h=s.Poly(G.reduce(s.expand(f))[1],X,Y)
    assert all(a in [(0,0),(1,0),(0,1),(2,0)] for a,_ in h.terms())
    return s.Matrix([h.coeff_monomial(b) for b in basis])
MX=s.Matrix.hstack(*(coords(X*b) for b in basis))
MY=s.Matrix.hstack(*(coords(Y*b) for b in basis))
mat=[s.eye(4),MX,MY,MX**2]
gram=s.Matrix([[s.trace(a*b) for b in mat] for a in mat])
delta=s.factor(gram.det())
q=4*X**2+2*Y**2+w*X-z*Y
Mq=s.Matrix.hstack(*(coords(q*b) for b in basis))
assert s.expand(Mq.det()+8*delta)==0
C=s.Matrix([[u*w/4,-v/2,2*u,(-3*u*z+v*w)/4],
            [3*u*z,4*u-w*z,2*v,(-u*w-v*z+w*w*z)/2],
            [(8*v-w*w)/4,-3*z,w,(16*u+5*w*z)/4],
            [-4*u,3*w/2,z,(4*v-3*w*w)/4]])
assert s.expand(C.det()-delta)==0
grad=s.Matrix([[s.diff(delta,t) for t in [u,v,w,z]]])
assert (grad*(-C)-delta*s.Matrix([[w/2,0,-8,3*z/2]])).applyfunc(s.expand)==s.zeros(1,4)
change=s.Matrix.hstack(*(coords(f) for f in [1,X,X**2,X**3]))
assert s.factor(change.det())==-u/2
p=2*X**4+w*X**3+v*X**2+z*u*X-u*u
assert s.expand(s.discriminant(p,X)-16*u*u*delta)==0
assert s.gcd(delta,s.diff(delta,u))==1
sample={u:1,v:-7,w:0,z:6}
foldgrad=[s.diff(delta,t).subs(sample) for t in [u,v,w,z]]
assert any(foldgrad)
J=s.Matrix([[Y,X],[-4*X-w,2*Y-z]])
assert s.expand(J.det()-q)==0
assert (J*J.adjugate()-q*s.eye(2)).applyfunc(s.expand)==s.zeros(2)
point={X:1,Y:1,w:0,z:6}
assert s.Matrix([[s.diff(q,t) for t in [X,Y,w,z]]]).subs(point)==s.Matrix([[8,-2,1,-1]])
# Polynomial map f:(X,Y,w,z)->(u,v,w,z), restricted to the tangent of q=0.
f=s.Matrix([X*Y,Y**2-2*X**2-w*X-z*Y,w,z])
assert f.subs(point)==s.Matrix([1,-7,0,6])
assert (s.Matrix.vstack(f.jacobian([X,Y,w,z]),s.Matrix([[s.diff(q,t) for t in [X,Y,w,z]]]))).subs(point).rank()==4
report={'status':'PASS','construction':'Groebner normal forms in QQ[u,v,w,z][Y,X], grevlex',
        'normal_forms':[str(g) for g in G.polys],
        'norm_q_over_trace_discriminant':-8,'quartic_discriminant_ratio':'16*u^2',
        'monogenic_basis_change_determinant':'-u/2',
        'fold_gradient_delta':[str(x) for x in foldgrad],
        'saito_derivative_identity_verified':True,'adjugate_injection_identity_verified':True,
        'polynomial_delta_squarefree':True,
        'primary_script_imported':False,
        'scope':'Exact polynomial identities; the normality, norm-length birationality, torsion-free embedding and finite endomorphism arguments are audited separately in prose.'}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--write-certificate',action='store_true')
args=parser.parse_args()
dest=HERE/'four_cover_discriminant_independent_audit.json'
if args.write_certificate:dest.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
else:assert json.loads(dest.read_text())==report
print(json.dumps({'status':'PASS','norm_ratio':-8,'quartic_ratio':'16*u^2',
                  'monogenic_basis_change':'-u/2'},ensure_ascii=False))
