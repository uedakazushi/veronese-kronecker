"""A formally etale self-opposite chart at B_minus (signature 1,5).

All 60 symmetry equations are imposed; the 60 pivot variables are solved
p-adically, with the other 93 variables chosen over Q near the base point.
This file constructs a reproducible exact algebraic point via Hensel's lemma.
"""
from pathlib import Path
from collections import defaultdict
import json, random, sys, time
sys.dont_write_bytecode=True
from flint import fmpz_mat, fmpz_mod_mat, fmpz_mod_ctx, nmod_mat

if not __debug__:
    raise RuntimeError('This exact verifier requires assertions; do not use python -O.')

ROOT=Path(__file__).resolve().parent
POS=2
NEG=[0,1,3,4,5]
AI={};ct=126
for u in range(7):
    for v in range(u,7):
        if (u,v)!=(6,6):
            AI[u,v]=AI[v,u]=ct;ct+=1
NVAR=ct
assert NVAR==153

def li(i,u,e):return (i*6+u)*7+e

def quadterms(i,u,j,v,sign,poly):
    for e in range(7):
        for f in range(7):
            inds=[li(i,u,e),li(j,v,f)]
            if (e,f)!=(6,6):inds.append(AI[e,f])
            poly[tuple(sorted(inds))]+=sign

def equations():
    out=[]
    for i in range(3):
        for j in range(i,3):
            for u in NEG:
                poly=defaultdict(int)
                quadterms(i,POS,j,u,1,poly)
                if i!=j:quadterms(j,POS,i,u,1,poly)
                out.append([(mon,c) for mon,c in sorted(poly.items()) if c])
    for i in range(3):
        for j in range(i+1,3):
            for ui,u in enumerate(NEG):
                for v in NEG[ui+1:]:
                    poly=defaultdict(int)
                    quadterms(i,u,j,v,1,poly)
                    quadterms(j,u,i,v,-1,poly)
                    out.append([(mon,c) for mon,c in sorted(poly.items()) if c])
    assert len(out)==60
    return out

EQS=equations()

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

def jacobian(vals, cols=None,mod=None):
    cols=list(range(NVAR)) if cols is None else cols
    pos={c:i for i,c in enumerate(cols)}
    rows=[]
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

def base_values():
    vals=[0]*NVAR
    # Entries (outer index, row, relation column, coefficient) of L_minus.
    entries=[(2,2,0,1),(0,5,0,1),(1,1,1,-1),(0,3,1,1),
             (2,4,2,-1),(1,5,2,1),(1,0,3,1),(0,1,3,1),
             (2,3,4,1),(1,4,4,1),(2,0,5,1),(0,2,5,-1),
             (2,1,6,1),(1,2,6,1),(0,4,6,1)]
    for i,u,e,c in entries:vals[li(i,u,e)]=c
    for u,v,c in [(0,1,1),(2,3,-1),(4,5,1)]:vals[AI[u,v]]=c
    assert not any(eval_eq(vals))
    return vals

def pivots_mod(rows,p):
    rows=[[x%p for x in r] for r in rows];piv=[];r=0
    for j in range(len(rows[0])):
        k=next((k for k in range(r,len(rows)) if rows[k][j]),None)
        if k is None:continue
        rows[r],rows[k]=rows[k],rows[r]
        co=pow(rows[r][j],-1,p)
        rows[r]=[(x*co)%p for x in rows[r]]
        for k in range(r+1,len(rows)):
            co=rows[k][j]
            if co:rows[k]=[(a-co*b)%p for a,b in zip(rows[k],rows[r])]
        piv.append(j);r+=1
        if r==len(rows):break
    return piv

def unpack(vals):
    L=[[[vals[li(i,u,e)] for e in range(7)] for u in range(6)] for i in range(3)]
    A=[[vals[AI[u,v]] if (u,v)!=(6,6) else 1 for v in range(7)] for u in range(7)]
    return L,A

def construct(p=101,precision=1024,seed=17029,save=True):
    base=base_values()
    piv=pivots_mod(jacobian(base),p)
    assert len(piv)==60
    jacobian_determinant=int(fmpz_mat(jacobian(base,piv)).det())
    assert jacobian_determinant==2
    free=[i for i in range(NVAR) if i not in piv]
    rng=random.Random(seed)
    vals=list(base)
    free_values={}
    for i in free:
        vals[i]+=p*rng.randint(-2,2);free_values[i]=vals[i]
    e=1
    initial_inverse=nmod_mat(jacobian(base,piv,p),p).inv()
    inverse_rows=[[int(initial_inverse[i,j]) for j in range(60)] for i in range(60)]
    start=time.time()
    print('Jacobian rank60, free93, Hensel p,precision,seed',p,precision,seed,flush=True)
    while e<precision:
        ne=min(2*e,precision);mod=p**ne
        ctx=fmpz_mod_ctx(mod)
        eq=eval_eq(vals,mod)
        jac=fmpz_mod_mat(jacobian(vals,piv,mod),ctx)
        inv=fmpz_mod_mat(inverse_rows,ctx)
        identity=fmpz_mod_mat([[int(i==j) for j in range(60)] for i in range(60)],ctx)
        # Field-style elimination may choose a nonunit pivot over Z/p^n.
        # Newton inversion uses only ring operations and preserves units.
        for _ in range(2):inv=inv*(2*identity-jac*inv)
        assert jac*inv==identity
        delta=inv*fmpz_mod_mat([[-x%mod] for x in eq],ctx)
        for i,v in enumerate(piv):vals[v]=(vals[v]+int(delta[i,0]))%mod
        assert not any(eval_eq(vals,mod))
        inverse_rows=[[int(inv[i,j]) for j in range(60)] for i in range(60)]
        e=ne
        print('precision',e,'elapsed',round(time.time()-start,3),flush=True)
    L,A=unpack(vals)
    out={'p':p,'precision':precision,'seed':seed,'pivot_variables':piv,
         'free_values':free_values,'values':[str(v) for v in vals],
         'L':[[[str(v) for v in row] for row in mat] for mat in L],
         'pairing':[[str(v) for v in row] for row in A],
         'equation_count':60,'jacobian_rank_at_base':60,
         'jacobian_pivot_determinant_at_base':jacobian_determinant}
    path=ROOT/f'hensel_{p}_{precision}_{seed}.json'
    if save:
        path.write_text(json.dumps(out,indent=2)+'\n')
        print('saved',path,flush=True)
    return out

def main():
    p=int(sys.argv[1]) if len(sys.argv)>1 else 101
    precision=int(sys.argv[2]) if len(sys.argv)>2 else 1024
    seed=int(sys.argv[3]) if len(sys.argv)>3 else 17029
    construct(p,precision,seed)

if __name__=='__main__':main()
