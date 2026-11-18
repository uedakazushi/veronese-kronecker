#!/usr/bin/env python3
"""Exact, dependency-free checks for the weighted Poisson calculations (v31).

Only Fraction arithmetic is used.  This verifies polynomial identities on
bases and exact matrix ranks; the smooth-cubic theorem is proved in the TeX
file and is not inferred from these sample ranks.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from pathlib import Path
import argparse
import json


def monomials(d):
    return [(a, b, d-a-b) for a in range(d+1) for b in range(d-a+1)]


def add(*ps):
    out = {}
    for p in ps:
        for m, v in p.items():
            out[m] = out.get(m, Q(0)) + v
    return {m: v for m, v in out.items() if v}


def scale(a, p):
    return {m: a*v for m, v in p.items() if a*v}


def mul(p, q):
    out = {}
    for m, v in p.items():
        for n, w in q.items():
            mn = tuple(a+b for a, b in zip(m, n))
            out[mn] = out.get(mn, Q(0)) + v*w
    return {m: v for m, v in out.items() if v}


def diff(p, i):
    out = {}
    for m, v in p.items():
        if m[i]:
            n = list(m)
            n[i] -= 1
            out[tuple(n)] = v*m[i]
    return out


ZERO = {}
X = tuple({tuple(int(i == j) for i in range(3)): Q(1)} for j in range(3))


def vadd(*vs):
    return tuple(add(*(v[i] for v in vs)) for i in range(3))


def vscale(a, v):
    return tuple(scale(a, p) for p in v)


def dot(a, b):
    return add(*(mul(p, q) for p, q in zip(a, b)))


def cross(a, b):
    return tuple(add(mul(a[(i+1) % 3], b[(i+2) % 3]),
                     scale(-1, mul(a[(i+2) % 3], b[(i+1) % 3])))
                 for i in range(3))


def grad(p):
    return tuple(diff(p, i) for i in range(3))


def div(v):
    return add(*(diff(v[i], i) for i in range(3)))


def curl(v):
    return tuple(add(diff(v[(i+2) % 3], (i+1) % 3),
                     scale(-1, diff(v[(i+1) % 3], (i+2) % 3)))
                 for i in range(3))


def vf(v, p):
    return dot(v, grad(p))


def basis_vec(d):
    return [tuple({m: Q(1)} if i == j else {} for i in range(3))
            for j in range(3) for m in monomials(d)]


def pi_matrix(p):
    return [[{}, p[2], scale(-1, p[1])],
            [scale(-1, p[2]), {}, p[0]],
            [p[1], scale(-1, p[0]), {}]]


def lie_bivector(f, p):
    """Coefficient vector of [F,Pi] = L_F Pi, by tensor indices."""
    pm = pi_matrix(p)
    ans = []
    for i, j in [(1, 2), (2, 0), (0, 1)]:
        ans.append(add(vf(f, pm[i][j]),
                       *(scale(-1, mul(pm[k][j], diff(f[i], k)))
                         for k in range(3)),
                       *(scale(-1, mul(pm[i][k], diff(f[j], k)))
                         for k in range(3))))
    return tuple(ans)


def mixed(c, d, f):
    return add(scale(2, vf(f, c)), scale(-1, dot(cross(X, d), f)),
               scale(-1, mul(c, div(f))))


def rank(columns, rows):
    """Sparse exact column Gaussian elimination."""
    pivots = {}
    for column in columns:
        v = {i: Q(column.get(row, 0)) for i, row in enumerate(rows)
             if column.get(row, 0)}
        while v:
            lead = min(v)
            if lead not in pivots:
                coeff = v[lead]
                pivots[lead] = {i: a/coeff for i, a in v.items()}
                break
            coeff = v[lead]
            for i, a in pivots[lead].items():
                v[i] = v.get(i, Q(0)) - coeff*a
                if not v[i]:
                    del v[i]
    return len(pivots)


def vec_column(v):
    return {(i, m): a for i, p in enumerate(v) for m, a in p.items()}


def traceless_basis():
    ans = []
    for i in range(3):
        for j in range(3):
            if i != j:
                ans.append(tuple(X[j] if k == i else {} for k in range(3)))
    ans.extend([(X[0], scale(-1, X[1]), {}),
                (X[0], {}, scale(-1, X[2]))])
    return ans


def case_ranks(name, p):
    c, d = dot(X, p), curl(p)
    fs = basis_vec(4)
    quotient_fs = [f for f in fs if not (f[0] and next(iter(f[0]))[0] > 0)]
    assert len(quotient_fs) == 35
    r_full = rank([mixed(c, d, f) for f in fs], monomials(6))
    r_quotient = rank([mixed(c, d, f) for f in quotient_fs], monomials(6))
    assert r_full == r_quotient
    hamiltonian = [vscale(-1, cross(p, grad({m: Q(1)})))
                   for m in monomials(3)]
    euler = [tuple(mul(x, {m: Q(1)}) for x in X) for m in monomials(3)]
    rows = [(i, m) for i in range(3) for m in monomials(4)]
    shift_rank = rank([vec_column(v) for v in euler+hamiltonian], rows)-10
    return {
        "name": name,
        "mixed_map_rank": r_full,
        "quartic_kernel_before_Euler": 45-r_full,
        "quartic_kernel_mod_Euler": 35-r_full,
        "cubic_w_shift_rank_mod_Euler": shift_rank,
        "sl3_to_cubic_rank_at_c": rank([vf(v, c) for v in traceless_basis()], monomials(3)),
    }


def determinant(matrix):
    a = [[Q(x) for x in row] for row in matrix]
    det = Q(1)
    for i in range(len(a)):
        j = next((j for j in range(i,len(a)) if a[j][i]),None)
        if j is None:
            return Q(0)
        if j != i:
            a[i],a[j] = a[j],a[i]
            det = -det
        pivot = a[i][i]
        det *= pivot
        for j in range(i+1,len(a)):
            factor = a[j][i]/pivot
            for k in range(i+1,len(a)):
                a[j][k] -= factor*a[i][k]
            a[j][i] = Q(0)
    return det


def vertical_component_certificate():
    def exp(**kw):
        return tuple(kw.get(str(i),0) for i in range(3))
    def unit_monomial(component, m):
        return tuple({m:Q(1)} if i==component else {} for i in range(3))
    columns,labels,rows = [],[],[]
    for i in range(3):
        columns.append(unit_monomial(i,tuple(2 if j==i else 0 for j in range(3))))
        labels.append(f'a_{i+1}')
        rows.append(tuple(6 if j==i else 0 for j in range(3)))
    for i in range(3):
        for j in range(3):
            if i==j: continue
            columns.append(unit_monomial(i,tuple(int(k==i)+int(k==j) for k in range(3))))
            labels.append(f'b_{i+1}{j+1}')
            rows.append(tuple(2*int(k==i)+4*int(k==j) for k in range(3)))
    for i in range(3):
        for j in range(3):
            if i==j: continue
            columns.append(unit_monomial(i,tuple(2 if k==j else 0 for k in range(3))))
            labels.append(f'd_{i+1}{j+1}')
            rows.append(tuple(int(k==i)+5*int(k==j) for k in range(3)))
    for i in range(3):
        columns.append(unit_monomial(i,tuple(int(k!=i) for k in range(3))))
        labels.append(f'e_{i+1}')
        rows.append(tuple(4 if k==i else 1 for k in range(3)))
    f = tuple({tuple(4 if j==i else 0 for j in range(3)):Q(1)} for i in range(3))
    output_columns = [mixed(dot(X,p),curl(p),f) for p in columns]
    matrix = [[int(col.get(row,0)) for col in output_columns] for row in rows]
    det = determinant(matrix)
    assert det == -20155392
    assert rank(output_columns,monomials(6)) == 18
    return {
        'point_F':['x1^4','x2^4','x3^4'],
        'column_coefficient_labels':labels,
        'row_sextic_monomial_exponents':[list(row) for row in rows],
        'exact_minor_matrix':matrix,
        'exact_minor_determinant':int(det),
        'rank':18,
        'conclusion':'The p=0 linear 35-dimensional family is a generically smooth irreducible Poisson component.'
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--vertical-certificate",type=Path)
    args = parser.parse_args()

    ps, fs = basis_vec(2), basis_vec(4)
    for p in ps:
        c, d = dot(X, p), curl(p)
        assert not div(d)
        assert vadd(grad(c), vscale(-1, cross(X, d))) == vscale(3, p)

    # The mixed identity is bilinear in (p,F), hence these 810 checks are universal.
    for p in ps:
        c, d = dot(X, p), curl(p)
        for f in fs:
            assert dot(X, lie_bivector(f, p)) == mixed(c, d, f)

    # Quadratic identity: checks on basis vectors and their pairwise sums suffice.
    for i, j in combinations_with_replacement(range(len(ps)), 2):
        p = ps[i] if i == j else vadd(ps[i], ps[j])
        c, d = dot(X, p), curl(p)
        assert scale(3, dot(p, d)) == vf(d, c)

    # Euler additions leave the mixed equation unchanged, universally in p and g.
    for p in ps:
        c, d = dot(X, p), curl(p)
        for m in monomials(3):
            f = tuple(mul(x, {m: Q(1)}) for x in X)
            assert not mixed(c, d, f)

    fermat = add(*({tuple(3 if i == j else 0 for i in range(3)): Q(1)}
                   for j in range(3)))
    p_fermat = vscale(Q(1, 3), grad(fermat))
    for m in monomials(3):
        g = {m: Q(1)}
        f = cross(grad(fermat), grad(g))
        assert not mixed(fermat, ({}, {}, {}), f)
        # w' = w+3g gives F+3*Pi(dg)=0 for F=grad(c) cross grad(g).
        pm = pi_matrix(p_fermat)
        pi_dg = tuple(add(*(mul(pm[i][j], diff(g, j)) for j in range(3)))
                      for i in range(3))
        assert vadd(f, vscale(3, pi_dg)) == ({}, {}, {})

    yz, zx, xy = mul(X[1], X[2]), mul(X[2], X[0]), mul(X[0], X[1])
    cases = [case_ranks("smooth_Fermat", p_fermat),
             case_ranks("generic_logcanonical_2_3_5", (scale(2,yz),scale(3,zx),scale(5,xy))),
             case_ranks("triangle_Jacobian", (yz,zx,xy))]
    fermat_case = cases[0]
    assert fermat_case["mixed_map_rank"] == 26
    assert fermat_case["quartic_kernel_mod_Euler"] == 9
    assert fermat_case["cubic_w_shift_rank_mod_Euler"] == 9
    assert fermat_case["sl3_to_cubic_rank_at_c"] == 8
    alpha, eig, total = (2,3,5), (2,-3,1), 10
    resonances = [list(m) for m in monomials(3) if sum(a*b for a,b in zip(eig,m)) == 0]
    assert resonances == [[1,1,1]]
    assert all(tuple(3*a-total*b for a,b in zip(alpha,m)) != (0,0,0)
               for m in monomials(3))
    assert all(3*a+total != 0 for a in alpha)
    assert cases[1]["mixed_map_rank"] == 25
    assert cases[1]["quartic_kernel_mod_Euler"] == 10
    assert cases[1]["cubic_w_shift_rank_mod_Euler"] == 10
    assert cases[2]["quartic_kernel_mod_Euler"] == 11
    assert cases[2]["cubic_w_shift_rank_mod_Euler"] == 9
    vertical = vertical_component_certificate()

    output = {
        "arithmetic": "fractions.Fraction over Q; no floating-point arithmetic",
        "normal_form_dimensions": {"quadratic_pi":18,"quartic_F":45,"Euler_gauge":10,"total":53},
        "universal_bilinear_mixed_identity_basis_checks": len(ps)*len(fs),
        "universal_quadratic_jacobi_identity_checks": len(ps)*(len(ps)+1)//2,
        "universal_Euler_gauge_checks": len(ps)*len(monomials(3)),
        "smooth_cubic_poisson_stratum_dimension": 19,
        "smooth_cubic_poisson_equation_jacobian_rank": 34,
        "cases": cases,
        "generic_logcanonical_cubic_resonances": resonances,
        "generic_logcanonical_negative_character_coefficients": [3*a+total for a in alpha],
        "vertical_component_dimension":35,
        "vertical_component_normal_rank":vertical['rank'],
        "vertical_component_exact_minor_determinant":vertical['exact_minor_determinant'],
        "all_assertions_passed": True,
        "scope": "Exact identities plus sample ranks; the general smooth-cubic theorem uses the independent Koszul proof."
    }
    text = json.dumps(output, ensure_ascii=False, indent=2)+"\n"
    print(text, end="")
    if args.output:
        args.output.write_text(text)
    if args.vertical_certificate:
        args.vertical_certificate.write_text(json.dumps(vertical,indent=2)+"\n")


if __name__ == "__main__":
    main()
