"""Certify finite etale length21 for the algebraic Hensel point.

The seven sextics' degree6 coefficients have invertible determinant over
Q_101. They reduce every degree6 monomial to degree<=5. Hilbert--Burch
therefore gives the 21-dimensional quotient. A multiplication matrix for
y is scaled by a power of 101 so that its entries are integral; a nonzero
characteristic-polynomial discriminant certifies reducedness.
"""
from pathlib import Path
import json,sys,time
from flint import fmpz_mod_mpoly_ctx,fmpz_mat,fmpz_mod_ctx,fmpz_mod_mat,fmpz_poly

if not __debug__:
    raise RuntimeError('This exact verifier requires assertions; do not use python -O.')

def valuation(a,p):
    a=int(a)
    if a==0:return 10**9
    out=0
    while a%p==0:a//=p;out+=1
    return out

def minor_polys(L,mod):
    ctx=fmpz_mod_mpoly_ctx.get(('x','y'),modulus=mod)
    x,y=ctx.gens()
    mat=[[int(L[0][u][e])*x+int(L[1][u][e])*y+int(L[2][u][e]) for e in range(7)] for u in range(6)]
    wedges={0:ctx.constant(1)}
    for u in range(6):
        nxt={}
        for mask,f in wedges.items():
            for e in range(7):
                if mask>>e&1:continue
                sign=-1 if (mask>>(e+1)).bit_count()%2 else 1
                key=mask|(1<<e)
                nxt[key]=nxt.get(key,ctx.constant(0))+sign*f*mat[u][e]
        wedges=nxt
    return [dict(poly.to_dict()) for mask,poly in sorted(wedges.items())]

def integral_residue(q,p,mod):
    a,b=int(q.numerator),int(q.denominator)
    v=valuation(b,p)
    assert a%p**v==0
    return ((a//p**v)*pow(b//p**v,-1,mod))%mod

def verify(raw,source='recomputed',save_path=None):
    p,N=raw['p'],raw['precision'];mod=p**N
    start=time.time()
    polys=minor_polys(raw['L'],mod)
    top=[(i,6-i) for i in range(7)]
    basis=[(i,d-i) for d in range(6) for i in range(d+1)]
    P=fmpz_mat([[int(f.get(m,0)) for m in top] for f in polys])
    C=fmpz_mat([[int(f.get(m,0)) for m in basis] for f in polys])
    det=P.det();vdet=valuation(det,p)
    assert vdet<N
    print('sextic top coefficient determinant valuation',vdet,flush=True)
    inv=P.inv()
    w=max(valuation(inv[i,j].denominator,p)-valuation(inv[i,j].numerator,p) for i in range(7) for j in range(7))
    w=max(w,0)
    prec=N-w;modout=p**prec;scale=p**w
    Q=fmpz_mod_mat([[integral_residue(scale*inv[i,j],p,modout) for j in range(7)] for i in range(7)],fmpz_mod_ctx(modout))
    D=-(Q*fmpz_mod_mat([[int(C[i,j])%modout for j in range(21)] for i in range(7)],fmpz_mod_ctx(modout)))
    assert all(int((Q*fmpz_mod_mat([[int(P[i,j])%modout for j in range(7)] for i in range(7)],fmpz_mod_ctx(modout)))[i,j]) == (scale if i==j else 0)%modout for i in range(7) for j in range(7))
    M=[[0]*21 for _ in range(21)]
    for j,(a,b) in enumerate(basis):
        target=(a,b+1)
        if a+b<5:M[basis.index(target)][j]=scale
        else:
            row=top.index(target)
            for i in range(21):M[i][j]=int(D[row,i])
    matrix=fmpz_mod_mat(M,fmpz_mod_ctx(modout))
    char=matrix.charpoly()
    cf=[int(v) for v in char.coeffs()]
    disc=fmpz_poly(cf).discriminant()
    vd=valuation(disc,p)
    print('inverse denominator exponent',w,'charpoly discriminant valuation',vd,'available precision',prec,'elapsed',round(time.time()-start,3),flush=True)
    out={'source':source,'prime':p,'input_precision':N,'top_coefficient_determinant_valuation':vdet,
         'inverse_denominator_exponent':w,'scaled_multiplication_precision':prec,
         'scaled_y_characteristic_polynomial_coefficients_mod_p_precision':[str(c) for c in cf],
         'scaled_y_discriminant_valuation':vd,'certified_reduced':vd<prec,
         'certified_length':21,'basis_monomials':basis}
    if save_path is not None:
        save_path.write_text(json.dumps(out,indent=2)+'\n')
        print('saved',save_path,flush=True)
    assert vd<prec,'increase p-adic precision'
    return out

def main():
    path=Path(sys.argv[1]);raw=json.loads(path.read_text())
    verify(raw,path.name,path.with_name(path.stem+'_geometry.json'))

if __name__=='__main__':main()
