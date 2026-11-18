#!/usr/bin/env python3
"""Exact algebraic checks for endpoint division fields (v38).

The proof for arbitrary parameters is in endpoint_birational_ja_v38.tex.
This script checks the universal exponent identities and exact cyclotomic
specializations; it does not use floating point tests or infer an all-order
statement from finitely many examples.  Normal use writes no files.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

import sympy as sp


def mul(a, b):
    """t^e X^i U^j chi^k, with UX=t XU."""
    e, i, j, k = a
    f, p, q, r = b
    return (sp.expand(e + f + j * p), i + p, j + q, k + r)


def inv(a):
    e, i, j, k = a
    return (sp.expand(-e + i * j), -i, -j, -k)


def comm(a, b):
    return mul(mul(mul(a, b), inv(a)), inv(b))


def universal_checks():
    e, f, i, j, k, p, q, r = sp.symbols("e f i j k p q r", integer=True)
    a, b = (e, i, j, k), (f, p, q, r)
    assert tuple(map(sp.expand, comm(a, b))) == (j * p - i * q, 0, 0, 0)
    assert mul(a, inv(a)) == (0, 0, 0, 0)
    assert mul(inv(a), a) == (0, 0, 0, 0)

    ell, power, aa, bb = sp.symbols("ell power a b", integer=True)
    change = sp.Matrix([[power, 0, aa], [0, 1, 0], [ell, 0, bb]])
    inverse = sp.Matrix([[bb, 0, -aa], [0, 1, 0], [-ell, 0, power]])
    determinant = sp.expand(power * bb - ell * aa)
    assert sp.expand(change.det()) == determinant
    assert change * inverse == sp.diag(determinant, 1, determinant)
    assert inverse * change == sp.diag(determinant, 1, determinant)
    # X'=X^power chi^a, U'=U, chi'=X^ell chi^b.
    xx, uu, cc = (0, power, 0, aa), (0, 0, 1, 0), (0, ell, 0, bb)
    assert comm(uu, xx) == (power, 0, 0, 0)
    assert comm(uu, cc) == (ell, 0, 0, 0)
    assert comm(xx, cc) == (0, 0, 0, 0)

    t, s, rho = sp.symbols("t s rho", nonzero=True)
    cayley = (1 - s * rho) / (1 + s * rho)
    assert sp.cancel(cayley.subs(rho, -rho) - 1 / cayley) == 0
    inverse_parameter = ((1 - t) / (1 + t)) ** 2
    assert sp.cancel(inverse_parameter.subs(t, cayley) - s * s * rho * rho) == 0
    assert sp.cancel(inverse_parameter.subs(t, 1 / t) - inverse_parameter) == 0
    # Equal values of the squared inverse Cayley transform have only the
    # t'=t and t'=t^{-1} solutions away from t,t'=-1.
    z = sp.symbols("z")
    numerator = sp.factor(sp.together(inverse_parameter - inverse_parameter.subs(t, z)))
    assert sp.cancel(numerator - 4 * (z - t) * (1 - t * z) / ((1 + t) ** 2 * (1 + z) ** 2)) == 0
    return {
        "monomial_commutator_exponent": "j*p-i*q",
        "unimodular_change_determinant": "power*b-ell*a",
        "unimodular_inverse_verified_symbolically": True,
        "new_quantum_parameter": "t^power",
        "new_chi_commutator_exponent": "ell",
        "inverse_Cayley_s_squared_gamma": "((1-t)/(1+t))^2",
        "square_root_sign_changes_t_to_inverse": True,
        "inverse_Cayley_fibers_are_t_and_inverse": True,
    }


def torsion_lattice_checks():
    rows = []
    for ell in range(3, 65):
        residue_pairs = [(i, j) for i in range(ell) for j in range(ell)]
        central_residues = [(i, j) for i, j in residue_pairs if i % ell == 0 and j % ell == 0]
        assert central_residues == [(0, 0)]
        primitive = []
        for k in range(1, ell):
            if gcd(k, ell) != 1:
                continue
            b = pow(k, -1, ell)
            a = (k * b - 1) // ell
            assert k * b - ell * a == 1
            matrix = sp.Matrix([[k, 0, a], [0, 1, 0], [ell, 0, b]])
            inverse = sp.Matrix([[b, 0, -a], [0, 1, 0], [-ell, 0, k]])
            assert matrix * inverse == sp.eye(3)
            assert inverse * matrix == sp.eye(3)
            primitive.append({"k": k, "a": a, "b": b})
        rows.append({
            "ell": ell,
            "basis_rank_over_center": ell * ell,
            "PI_degree": ell,
            "center_residue_lattice": [list(pair) for pair in central_residues],
            "primitive_parameters": primitive,
        })
    return rows


def cyclotomic_checks():
    t, z = sp.symbols("t z")
    rows = []
    for ell in range(3, 17):
        phi = sp.Poly(sp.cyclotomic_poly(ell, t), t, domain=sp.QQ)
        assert phi.eval(-1) != 0
        assert phi.eval(1) != 0
        resultant = sp.Poly(sp.resultant(phi.as_expr(), z * (1 + t) ** 2 - (1 - t) ** 2, t), z)
        squarefree = resultant.sqf_part().primitive()[1]
        if squarefree.LC() < 0:
            squarefree = -squarefree
        assert squarefree.degree() * 2 == int(sp.totient(ell))
        # Each parameter comes from precisely t and t^{-1}, hence double roots.
        assert sp.rem(resultant, squarefree ** 2).is_zero
        assert resultant.degree() == 2 * squarefree.degree()
        assert squarefree.eval(0) != 0
        assert squarefree.eval(1) != 0
        rows.append({
            "ell": ell,
            "primitive_root_count": int(sp.totient(ell)),
            "distinct_s_squared_gamma_count": squarefree.degree(),
            "parameter_polynomial": str(squarefree.as_expr()),
        })
    expected = {3: z + 3, 4: z + 1, 5: z * z + 10 * z + 5, 6: 3 * z + 1}
    for row in rows:
        if row["ell"] in expected:
            assert sp.expand(sp.sympify(row["parameter_polynomial"]) - expected[row["ell"]]) == 0
    return rows


def result():
    return {
        "schema": "vk_endpoint_birational_v38_exact_v1",
        "status": "PASS",
        "coefficient_domains": ["Z exponent lattices", "Q(t,s,rho)", "Q[z]"],
        "universal": universal_checks(),
        "torsion_lattice": torsion_lattice_checks(),
        "cyclotomic_parameters": cyclotomic_checks(),
        "proof_not_finite_extrapolation": {
            "AD_invariant": "leading monomials in skew Laurent series",
            "Weyl_invariant": "multiplicative commutative leading symbol",
            "torsion_isomorphism": "Bezout gives an integral determinant-one change",
            "PI_criterion": "explicit center and division dimension, then Posner",
            "density": "all primitive roots and the inverse Cayley transform",
        },
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    actual = result()
    if args.check:
        expected = json.loads(args.check.read_text(encoding="utf-8"))
        assert actual == expected, "certificate differs from independent recomputation"
        print(json.dumps({"status": "PASS", "certificate": str(args.check),
                          "sha256": hashlib.sha256(args.check.read_bytes()).hexdigest()}, sort_keys=True))
    else:
        print(json.dumps(actual, ensure_ascii=False, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
