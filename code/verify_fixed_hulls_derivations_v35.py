#!/usr/bin/env python3
"""Exact QQ checks of HH^1 for fixed CGG Beilinson algebras.

No external dependencies. Ordinary execution is read-only. --write-certificate
is an explicit authoring operation and is never used for verification.

Derivations fixing all vertices are determined by the images of degree-one
arrows and the three degree-m arrows w. We differentiate the quadratic and
degree-(m+1) Ore relations and evaluate them in the actual finite CGG product.
The manuscript proves that these relations present the algebra and proves
the all-weight hull theorem independently of these finite rank checks.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from math import comb
from pathlib import Path

ZERO=()
UNIT=(((0,0,0,0),F(1)),)
GEN=tuple((((int(i==0),int(i==1),int(i==2),int(i==3)),F(1)),) for i in range(4))

def canonical(data):
    return tuple(sorted((e,F(c)) for e,c in data.items() if c))

def add(*terms):
    out={}
    for p in terms:
        for e,c in p:out[e]=out.get(e,F(0))+c
    return canonical(out)

def scale(c,p):
    return tuple((e,c*v) for e,v in p if c*v)

def mul(p,q):
    out={}
    for e,c in p:
        for f,d in q:
            g=tuple(a+b for a,b in zip(e,f))
            out[g]=out.get(g,F(0))+c*d
    return canonical(out)

def monomial(e):return ((tuple(e),F(1)),)

def binom(a,n):
    ans=F(1)
    for i in range(n):ans*=F(a-i,i+1)
    return ans

def weighted_basis(degree,m):
    return [(a,b,degree-m*w-a-b,w)
            for w in range(degree//m+1)
            for a in range(degree-m*w+1)
            for b in range(degree-m*w-a+1)]

class Algebra:
    def __init__(self,j,r,alpha,s=1,variant='q'):
        self.j,self.r,self.m=j,r,2*j+r
        self.alpha,self.s=F(alpha),F(s)
        self.d=self.m+r+1
        self.weights=(self.alpha,self.alpha+1,self.alpha+2,self.m*self.alpha+self.d)
        if variant=='q':
            self.p=canonical({(k,2*(j-k),r+k,0):F((-1)**(j-k)*comb(j,k)) for k in range(j+1)})
        elif variant=='y':self.p=monomial((0,2*j,r,0))
        else:raise ValueError(variant)
        self.variant=variant

    @lru_cache(None)
    def n(self,p):
        out=[]
        for e,c in p:
            a,b,z,w=e
            if b:out.append(scale(c*b,monomial((a+1,b-1,z,w))))
            if z:out.append(scale(2*c*z,monomial((a,b+1,z-1,w))))
            if w:out.append(scale(-c*w,mul(monomial((a,b,z,w-1)),self.p)))
        return add(*out)

    @lru_cache(None)
    def star(self,p,q):
        result=ZERO;current=p;n=0
        while current:
            b=canonical({e:c*binom(sum(i*a for i,a in zip(e,self.weights)),n) for e,c in q})
            result=add(result,scale(self.s**n,mul(current,b)))
            current=self.n(current);n+=1
            if n>100:raise AssertionError('local nilpotence failed')
        return result

    @lru_cache(None)
    def word(self,word):
        p=UNIT
        for i in word:p=self.star(p,GEN[i])
        return p

    def pure_ordered(self,p,degree):
        """Triangular inverse: star corrections strictly lower auxiliary weight."""
        result={};remaining=p
        for e in sorted(weighted_basis(degree,self.m),key=lambda e:(e[1]+2*e[2]+self.d*e[3],e),reverse=True):
            if e[3]:continue
            c=dict(remaining).get(e,F(0))
            if not c:continue
            word=(0,)*e[0]+(1,)*e[1]+(2,)*e[2]
            result[word]=c
            remaining=add(remaining,scale(-c,self.word(word)))
        if remaining:raise AssertionError(('ordered basis failed',remaining))
        return result

    def relations(self):
        a,s=self.alpha,self.s
        quadratics=[
            {(1,0):F(1),(0,1):F(-1),(0,0):-s*a},
            {(2,0):F(1),(0,2):F(-1),(0,1):-2*s*a,(0,0):-s*s*a*(a-1)},
            {(2,1):F(1),(1,2):F(-1),(1,1):-2*s*(a+1),(0,2):s*(a+2),(0,1):s*s*(a+1)*(a+2)}]
        lam=self.weights[3]
        tau=[{0:F(1)},{1:F(1),0:-lam*s},{2:F(1),1:-2*lam*s,0:lam*(lam+1)*s*s}]
        mixed=[]
        for i in range(3):
            relation={(3,i):F(1)}
            for k,c in tau[i].items():relation[(k,3)]=relation.get((k,3),F(0))-c
            delta=add(*(scale(c,self.word(w)) for w,c in relation.items()))
            assert all(e[3]==0 for e,c in delta)
            for w,c in self.pure_ordered(delta,self.m+1).items():relation[w]=relation.get(w,F(0))-c
            mixed.append(relation)
        for relation in quadratics+mixed:
            value=add(*(scale(c,self.word(w)) for w,c in relation.items()))
            assert not value,('nonzero relation',value)
        return quadratics,mixed

def rank_qq(rows):
    """Exact forward elimination over QQ, retaining a deterministic pivot list."""
    mat=[list(row) for row in rows]
    n=len(mat);m=len(mat[0]) if n else 0
    rank=0;pivots=[]
    for col in range(m):
        pivot=next((i for i in range(rank,n) if mat[i][col]),None)
        if pivot is None:continue
        mat[rank],mat[pivot]=mat[pivot],mat[rank]
        v=mat[rank][col]
        mat[rank]=[x/v for x in mat[rank]]
        for i in range(rank+1,n):
            a=mat[i][col]
            if a:
                for k in range(col+1,m):mat[i][k]-=a*mat[rank][k]
                mat[i][col]=F(0)
        pivots.append(col);rank+=1
        if rank==n:break
    return rank,pivots

def case(j,r,alpha=None,s=1,variant='q'):
    m=2*j+r
    if alpha is None:alpha=F(-(m+r+3),m+3)
    alg=Algebra(j,r,alpha,s,variant)
    quadratic,mixed=alg.relations()
    variables=[]
    for start in range(m+2):
        for gen in range(3):
            for target in range(3):variables.append((start,gen,GEN[target]))
    for start in range(3):
        for e in weighted_basis(m,m):variables.append((start,3,monomial(e)))
    var_index={(start,gen,p):i for i,(start,gen,p) in enumerate(variables)}
    choices={}
    for index,(start,gen,p) in enumerate(variables):choices.setdefault((start,gen),[]).append((index,p))
    rows=[]; relation_instances=0
    for degree,relations in [(2,quadratic),(m+1,mixed)]:
        basis=weighted_basis(degree,m)
        output_index={e:i for i,e in enumerate(basis)}
        for start in range(m+3-degree):
            for relation in relations:
                block=[[F(0) for _ in variables] for _ in basis]
                for word,c in relation.items():
                    position=start
                    for slot,gen in enumerate(word):
                        pre,suf=alg.word(word[:slot]),alg.word(word[slot+1:])
                        for col,p in choices[(position,gen)]:
                            value=alg.star(alg.star(pre,p),suf)
                            for e,v in value:block[output_index[e]][col]+=c*v
                        position+=m if gen==3 else 1
                rows.extend(block);relation_instances+=1
    rank,pivots=rank_qq(rows)
    derivations=len(variables)-rank
    expected_hh1=(comb(m+2,2)+9) if F(s)==0 else 1
    inner_dimension=m+2
    assert derivations==expected_hh1+inner_dimension,(j,r,alpha,s,variant,derivations)
    # All vertex-inner derivations must satisfy the differentiated relations.
    inner=[]
    for vertex in range(1,m+3):
        vector=[F(0) for _ in variables]
        for index,(start,gen,p) in enumerate(variables):
            end=start+(m if gen==3 else 1)
            if p==GEN[gen]:vector[index]=F(int(end==vertex)-int(start==vertex))
        assert all(sum(a*b for a,b in zip(row,vector))==0 for row in rows)
        inner.append(vector)
    assert rank_qq(list(map(list,zip(*inner))))[0]==inner_dimension
    # Explicit normalized log(T) is a derivation and adds one outer direction.
    log_vector=[F(0) for _ in variables]
    for start,gen in sorted(choices):
        current=alg.n(GEN[gen]);n=1;value=ZERO
        while current:
            value=add(value,scale(F((-1)**(n+1),n)*F(s)**(n-1),current))
            current=alg.n(current);n+=1
        for col,p in choices[(start,gen)]:
            e=p[0][0]
            log_vector[col]=dict(value).get(e,F(0))
    assert all(sum(a*b for a,b in zip(row,log_vector))==0 for row in rows)
    assert rank_qq(list(map(list,zip(*(inner+[log_vector])))))[0]==inner_dimension+1
    encoded='\n'.join(','.join(str(c) for c in row) for row in rows).encode()
    return {
        'm':m,'j':j,'r':r,'alpha':str(F(alpha)),'s':str(F(s)),'variant':variant,
        'vertices':m+3,'minimal_arrows':3*(m+2)+3,
        'derivation_image_variables':len(variables),'differentiated_relations':relation_instances,
        'scalar_equations':len(rows),'matrix_rank_QQ':rank,'kernel_dimension_QQ':derivations,
        'inner_derivation_dimension':inner_dimension,'HH1_dimension':expected_hh1,
        'matrix_sha256':sha256(encoded).hexdigest(),'pivot_columns':pivots,
        'all_six_relation_types_vanish':True,
        'vertex_inner_derivations_verified':True,'normalized_log_T_verified_outer':True,
        'expected_hull_length_from_structural_theorem':j+1 if F(s)!=0 else None
    }

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-certificate',action='store_true')
    args=parser.parse_args()
    cases=[
        case(0,3,s=0),case(0,3),case(1,1),case(1,1,variant='y'),
        case(1,1,alpha=0),case(1,1,alpha=-1),case(1,1,s=F(-1,2)),
        case(0,4),case(1,2),case(2,1)]
    result={'status':'PASS','version':35,'coefficient_field':'QQ',
        'scope':'Finite checks of derivation spaces for full standard Beilinson algebras. The all-weight deformation-hull theorem uses the manuscript formal arc transfer proof, not extrapolation of these ranks.',
        'case_count':len(cases),'cases':cases}
    text=json.dumps(result,ensure_ascii=False,indent=2)+'\n'
    certificate=Path(__file__).with_name('fixed_hulls_derivations_v35_certificate.json')
    if args.write_certificate:
        certificate.write_text(text,encoding='utf-8')
    else:
        expected=json.loads(certificate.read_text(encoding='utf-8'))
        assert result==expected, 'full recomputed JSON differs from the stored certificate'
    print(text,end='')

if __name__=='__main__':main()
