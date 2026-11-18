#!/usr/bin/env python3
"""Universal exact BV checks for weights (1,1,1,3), without dependencies."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse
import json

WEIGHTS = (1, 1, 1, 3)
N = len(WEIGHTS)


def monomials(degree):
    return [(a,b,c,d) for d in range(degree//3+1)
            for a in range(degree-3*d+1)
            for b in range(degree-3*d-a+1)
            for c in [degree-3*d-a-b]]


def add(*us):
    ans = {}
    for u in us:
        for key, value in u.items():
            ans[key] = ans.get(key, Q(0)) + value
    return {key: value for key, value in ans.items() if value}


def scale(a, u):
    return {key: a*value for key, value in u.items() if a*value}


def wedge(u, v):
    ans = {}
    for (ii,m), a in u.items():
        for (jj,n), b in v.items():
            if set(ii).intersection(jj):
                continue
            sign = (-1)**sum(i > j for i in ii for j in jj)
            key = (tuple(sorted(ii+jj)), tuple(x+y for x,y in zip(m,n)))
            ans[key] = ans.get(key, Q(0)) + sign*a*b
    return {key:value for key,value in ans.items() if value}


def delta(u):
    ans = {}
    for (ii,m), a in u.items():
        for position, i in enumerate(ii):
            if not m[i]:
                continue
            n = list(m)
            n[i] -= 1
            key = (ii[:position]+ii[position+1:],tuple(n))
            ans[key] = ans.get(key,Q(0)) + (-1)**position*m[i]*a
    return {key:value for key,value in ans.items() if value}


E = {((i,), tuple(int(i == j) for j in range(N))): Q(WEIGHTS[i])
     for i in range(N)}


def degree(u):
    return len(next(iter(u))[0]) if u else None


def schouten(u, v):
    if not u or not v:
        return {}
    k = degree(u)
    return scale((-1)**(k-1), add(delta(wedge(u,v)),
                                 scale(-1,wedge(delta(u),v)),
                                 scale(-(-1)**k,wedge(u,delta(v)))))


def lift(u):
    return add(u, scale(Q(-1,6), wedge(E,delta(u))))


def basis(k):
    return [{(ii,m): Q(1)} for ii in combinations(range(N),k)
            for m in monomials(sum(WEIGHTS[i] for i in ii))]


def exact_rank(columns):
    pivots = {}
    for column in columns:
        v = dict(column)
        while v:
            lead = min(v)
            if lead not in pivots:
                a = v[lead]
                pivots[lead] = {key:value/a for key,value in v.items()}
                break
            a = v[lead]
            for key,value in pivots[lead].items():
                v[key] = v.get(key,Q(0))-a*value
                if not v[key]:
                    del v[key]
    return len(pivots)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    bs = [basis(k) for k in range(5)]
    for b in sum(bs,[]):
        assert not delta(delta(b))
        assert add(delta(wedge(E,b)),wedge(E,delta(b))) == scale(6,b)
        assert not delta(lift(b))
        assert lift(lift(b)) == lift(b)
        assert wedge(E,lift(b)) == wedge(E,b)
    for b in sum(bs[:-1],[]):
        assert not lift(wedge(E,b))

    # Unimodular representatives close under Schouten brackets.  This is
    # universal by bilinearity, not a test on a few numerical examples.
    lifted_bis = [lift(b) for b in bs[2]]
    closure_count = 0
    for i,u in enumerate(lifted_bis):
        for v in lifted_bis[i:]:
            assert not delta(schouten(u,v))
            closure_count += 1

    ranks = [exact_rank([lift(b) for b in bk]) for bk in bs]
    assert ranks == [1,19,53,39,0]
    delta_ranks = [exact_rank([delta(b) for b in bk]) for bk in bs]
    assert delta_ranks == [0,1,19,53,39]
    out = {
        "weights": list(WEIGHTS),
        "weighted_volume_degree": 6,
        "polynomial_multivector_dimensions_k0_to_k4": [len(b) for b in bs],
        "divergence_ranks_k0_to_k4": delta_ranks,
        "unimodular_projection_ranks_k0_to_k4": ranks,
        "universal_homotopy_identity_checks": sum(len(b) for b in bs),
        "universal_vertical_annihilation_checks": sum(len(b) for b in bs[:-1]),
        "bivector_bracket_BV_closure_checks": closure_count,
        "all_assertions_passed": True,
        "claim": "delta(E wedge U)+E wedge delta(U)=6U for every weightzero polynomial multivector U; unique unimodular representative in every Euler quotient."
    }
    text = json.dumps(out,indent=2)+"\n"
    print(text,end="")
    if args.output:
        args.output.write_text(text)


if __name__ == "__main__":
    main()
