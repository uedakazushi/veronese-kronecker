"""Exact Hensel certificates for signatures (3,3) and (2,4).

Default execution compares a compact stored certificate without writing.
Use --write-certificate to regenerate that file explicitly.
"""
from pathlib import Path
from collections import defaultdict
import argparse,sys,json,random,time
import hensel_chart as hc
import hensel_points as hp
from flint import fmpz_mat,fmpz_mod_mat,fmpz_mod_ctx,nmod_mat,fmpq_mat,nmod_mpoly_ctx

if not __debug__:
    raise RuntimeError('Assertions must be enabled.')

EQS=[]

def eval_eq(vals,mod=None):
    out=[]
    for poly in EQS:
        tot=0
        for mon,c in poly:
            term=c
            for v in mon:term*=vals[v]
            tot+=term
        out.append(tot%mod if mod else tot)
    return out

def jacobian(vals,cols=None,mod=None):
    cols=list(range(hc.NVAR)) if cols is None else cols
    pos={c:i for i,c in enumerate(cols)};rows=[]
    for poly in EQS:
        row=[0]*len(cols)
        for mon,c in poly:
            for a,v in enumerate(mon):
                if v not in pos:continue
                term=c
                for b,w in enumerate(mon):
                    if b!=a:term*=vals[w]
                row[pos[v]]+=term
        rows.append([v%mod for v in row] if mod else row)
    return rows

def equations(p):
    plus=list(range(p));minus=list(range(p,6));out=[]
    for i in range(3):
        for j in range(i,3):
            for u in plus:
                for v in minus:
                    poly=defaultdict(int)
                    hc.quadterms(i,u,j,v,1,poly)
                    if i!=j:hc.quadterms(j,u,i,v,1,poly)
                    out.append([(mon,c) for mon,c in sorted(poly.items()) if c])
    for i in range(3):
        for j in range(i+1,3):
            for block in [plus,minus]:
                for ui,u in enumerate(block):
                    for v in block[ui+1:]:
                        poly=defaultdict(int)
                        hc.quadterms(i,u,j,v,1,poly)
                        hc.quadterms(j,u,i,v,-1,poly)
                        out.append([(mon,c) for mon,c in sorted(poly.items()) if c])
    return out

def prepare(p):
    global EQS
    base=hc.base_values();L,_=hc.unpack(base)
    if p==3:
        order=[1,2,4,0,3,5]
        newL=[[[L[i][u][e] for e in range(7)] for u in order] for i in range(3)]
    else:
        H=[[1,0,0,-1,0,0],[0,0,1,0,-1,0],
           [1,0,0,1,0,0],[0,0,1,0,1,0],
           [0,1,0,0,0,0],[0,0,0,0,0,1]]
        newL=[[[sum(H[u][v]*L[i][v][e] for v in range(6)) for e in range(7)]
               for u in range(6)] for i in range(3)]
    base=[0]*hc.NVAR
    for i in range(3):
        for u in range(6):
            for e in range(7):base[hc.li(i,u,e)]=newL[i][u][e]
    EQS=equations(p)
    # Solve the symmetric pairing linearly, normalized by A_77=1.
    cols=list(range(126,153));jac=jacobian(base,cols)
    rowpiv=hc.pivots_mod(list(map(list,zip(*jac))),101)
    assert len(rowpiv)==27
    A=fmpq_mat([jac[i] for i in rowpiv])
    rhs=fmpq_mat([[-eval_eq(base)[i]] for i in rowpiv])
    sol=A.inv()*rhs
    assert all(sol[i,0].denominator==1 for i in range(27))
    for i,c in enumerate(cols):base[c]=int(sol[i,0].numerator)
    assert not any(eval_eq(base))
    return base

def base_gates(base,pblock,prime=101):
    L,A=hc.unpack(base)
    J=[1]*pblock+[-1]*(6-pblock)
    R=[[[J[u]*L[i][u][e] for e in range(7)] for u in range(6)] for i in range(3)]
    wedge=[(u,v) for u in range(6) for v in range(u+1,6)]
    F=[[int(u==b)*L[i][a][e]-int(u==a)*L[i][b][e]
        for u in range(6) for e in range(7)] for i in range(3) for a,b in wedge]
    N=[[L[i][u][e]*int(k==j) for i in range(3) for u in range(6) for k in range(3)]
       for e in range(7) for j in range(3)]
    N += [[R[k][u][e]*int(h==i) for h in range(3) for u in range(6) for k in range(3)]
          for i in range(3) for e in range(7)]
    recovery=[[L[i][a][w]*R[j][b][v]-R[j][a][v]*L[i][b][w]
               for v in range(7) for w in range(7)]
              for i in range(3) for j in range(3) for a,b in wedge]
    ranks={'F':nmod_mat(F,prime).rank(),'N':nmod_mat(N,prime).rank(),
           'recovery':nmod_mat(recovery,prime).rank()}
    assert ranks=={'F':39,'N':36,'recovery':48}
    # All degree-p monomials belong to the span of the p-row block minors.
    # This is a direct certificate that the block has no rank-drop point,
    # even after extending the residue field algebraically.
    ctx=nmod_mpoly_ctx.get(('x','y','z'),modulus=prime);xx=ctx.gens()
    mat=[[sum((L[i][u][e]*xx[i] for i in range(3)),ctx.constant(0))
          for e in range(7)] for u in range(pblock)]
    polys={0:ctx.constant(1)}
    for u in range(pblock):
        nxt={}
        for mask,f in polys.items():
            for e in range(7):
                if mask>>e&1:continue
                key=mask|(1<<e)
                sign=-1 if (mask>>(e+1)).bit_count()%2 else 1
                nxt[key]=nxt.get(key,ctx.constant(0))+sign*f*mat[u][e]
        polys=nxt
    mons=[(a,b,pblock-a-b) for a in range(pblock+1) for b in range(pblock+1-a)]
    coefs=[[int(f.to_dict().get(m,0)) for m in mons] for f in polys.values()]
    rank=nmod_mat(coefs,prime).rank()
    assert rank==len(mons)
    return {'base_open_ranks_mod_p':ranks,'small_block_minor_span_degree':pblock,
            'small_block_minor_span_rank':rank,'small_block_minor_span_expected':len(mons)}

def construct(pblock,precision=None,seed=17029,write_certificate=False):
    if precision is None:precision=1536 if pblock==3 else 1024
    p=101;base=prepare(pblock);neq=len(EQS)
    gates=base_gates(base,pblock,p)
    piv=hc.pivots_mod(jacobian(base),p)
    print('signature',pblock,6-pblock,'equations',neq,'Jacobian rank',len(piv),flush=True)
    assert len(piv)==neq
    det=int(fmpz_mat(jacobian(base,piv)).det())
    print('Jacobian determinant',det,flush=True)
    free=[i for i in range(hc.NVAR) if i not in piv];rng=random.Random(seed)
    vals=list(base);free_values={}
    for i in free:
        vals[i]+=p*rng.randint(-2,2);free_values[i]=vals[i]
    initial=nmod_mat(jacobian(base,piv,p),p).inv()
    invrows=[[int(initial[i,j]) for j in range(neq)] for i in range(neq)]
    e=1;start=time.time()
    while e<precision:
        ne=min(2*e,precision);mod=p**ne;ctx=fmpz_mod_ctx(mod)
        eq=eval_eq(vals,mod);jac=fmpz_mod_mat(jacobian(vals,piv,mod),ctx)
        inv=fmpz_mod_mat(invrows,ctx)
        identity=fmpz_mod_mat([[int(i==j) for j in range(neq)] for i in range(neq)],ctx)
        for _ in range(2):inv=inv*(2*identity-jac*inv)
        assert jac*inv==identity
        delta=inv*fmpz_mod_mat([[-x%mod] for x in eq],ctx)
        for i,v in enumerate(piv):vals[v]=(vals[v]+int(delta[i,0]))%mod
        assert not any(eval_eq(vals,mod))
        invrows=[[int(inv[i,j]) for j in range(neq)] for i in range(neq)]
        e=ne
        print('precision',e,'elapsed',round(time.time()-start,3),flush=True)
    L,A=hc.unpack(vals)
    raw={'p':p,'precision':precision,'seed':seed,'signature':[pblock,6-pblock],
         'pivot_variables':piv,'free_values':free_values,'base_values':base,
         'values':[str(v) for v in vals],
         'L':[[[str(v) for v in row] for row in mat] for mat in L],
         'pairing':[[str(v) for v in row] for row in A],
         'equation_count':neq,'jacobian_determinant':det}
    geom=hp.verify(raw)
    path=Path(__file__).resolve().parent/f'hensel_signature_{pblock}_{6-pblock}_v24.json'
    summary={k:v for k,v in raw.items() if k not in ('L','pairing','values')}
    summary['free_direction']={str(i):(v-base[int(i)])//p for i,v in free_values.items()}
    summary['free_values']={str(i):v for i,v in free_values.items()}
    summary['geometry']={k:v for k,v in geom.items() if k!='scaled_y_characteristic_polynomial_coefficients_mod_p_precision'}
    summary['fixed_count']=3+(2*pblock-6)**2//2
    summary['nonfixed_pair_count']=(21-summary['fixed_count'])//2
    # The pairing and block independence conditions are units at the base.
    _,baseA=hc.unpack(base)
    summary['base_pairing_determinant']=int(fmpz_mat(baseA).det())
    assert summary['base_pairing_determinant']%p
    summary.update(gates)
    # JSON stores exponent pairs as lists, rather than Python tuples.
    summary=json.loads(json.dumps(summary))
    if write_certificate:
        path.write_text(json.dumps(summary,indent=2)+'\n')
    else:
        assert summary==json.loads(path.read_text()),'Certificate differs from exact regenerated data.'
    print('saved' if write_certificate else 'read-only certificate comparison PASS',path,flush=True)
    return summary

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('pblock',type=int,choices=[2,3])
    parser.add_argument('--write-certificate',action='store_true')
    args=parser.parse_args()
    construct(args.pblock,write_certificate=args.write_certificate)

if __name__=='__main__':main()
