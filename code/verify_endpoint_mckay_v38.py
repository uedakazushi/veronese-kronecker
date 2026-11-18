#!/usr/bin/env python3
"""Exact checks for the even-root McKay corner (v38).

The all-order proof uses the GWA direct sum, full idempotent argument, and
formal implicit function theorem. This read-only verifier checks the universal
formulas and finite exact implementation examples; it does not substitute
finite examples for those arguments.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import sympy as sp


def symbolic_checks():
    Q, lam, beta = sp.symbols("Q lam beta", nonzero=True)
    d = sp.symbols("d", integer=True, positive=True)
    f = (-1) ** d * Q ** d + beta ** d * lam ** (2 * d)
    F = Q ** d + (-1) ** d * beta ** d * lam ** (2 * d)
    assert sp.simplify(f - (-1) ** d * F) == 0
    assert sp.simplify(f * f - F * F) == 0
    assert sp.simplify(sp.diff(f, lam) - 2 * d * beta ** d * lam ** (2 * d - 1)) == 0
    assert sp.simplify(sp.diff(f, Q) - (-1) ** d * d * Q ** (d - 1)) == 0
    p, r, U, V, C = sp.symbols("p r U V C")
    gb = sp.groebner([U - p * p, V - r * r, C - p * r], p, r, U, V, C, order="lex")
    elimination = [g.as_expr() for g in gb.polys if not g.as_expr().has(p, r)]
    assert elimination == [U * V - C * C]
    return {
        "half_norm": "(-1)^d Q^d + beta^d lambda^(2d)",
        "half_norm_squared_matches_corrected_even_center": True,
        "smooth_cover_derivative_lambda": "2d beta^d lambda^(2d-1)",
        "implicit_Q_derivative": "(-1)^d d Q^(d-1)",
        "mu2_invariant_elimination": "U*V-C^2",
    }


def half_norm_checks():
    t = sp.symbols("t")
    rows = []
    for ell in range(4, 41, 2):
        d = ell // 2
        phi = sp.Poly(sp.cyclotomic_poly(ell, t), t, domain=sp.QQ)
        coeff = [sp.Poly(1, t, domain=sp.QQ)]
        for i in range(d):
            factor = sp.Poly(t ** (2 * i + 1), t, domain=sp.QQ).rem(phi)
            new = [sp.Poly(0, t, domain=sp.QQ) for _ in range(len(coeff) + 1)]
            for k, a in enumerate(coeff):
                new[k] = (new[k] - a).rem(phi)
                new[k + 1] = (new[k + 1] - a * factor).rem(phi)
            coeff = new
        assert coeff[0] == sp.Poly((-1) ** d, t, domain=sp.QQ)
        assert coeff[-1] == sp.Poly(1, t, domain=sp.QQ)
        assert all(a.is_zero for a in coeff[1:-1])
        # Corner e0+ed only retains degrees divisible by d.
        support = [n for n in range(ell) if any((j - n) % ell in {0, d} for j in (0, d))]
        assert support == [0, d]
        # Remove opposite zero edges i->i-1 and i+d->i+d-1.
        for cut in range(ell):
            adj = {i: set() for i in range(ell)}
            for i in range(ell):
                if i in {cut, (cut + d) % ell}:
                    continue
                j = (i - 1) % ell
                adj[i].add(j)
                adj[j].add(i)
            components = []
            unseen = set(range(ell))
            while unseen:
                start = min(unseen)
                comp, todo = set(), [start]
                while todo:
                    current = todo.pop()
                    if current in comp:
                        continue
                    comp.add(current)
                    todo.extend(adj[current] - comp)
                unseen -= comp
                components.append(comp)
            assert len(components) == 2
            assert sorted(map(len, components)) == [d, d]
            assert all(not ({0, d} <= comp) for comp in components)
        rows.append({"ell": ell, "d": d, "half_norm_coefficients": [str(a.as_expr()) for a in coeff],
                     "corner_residues": support, "fullness_graph_all_cut_positions": True})
    return rows


def product(a, b):
    """Normal word P^n g^e (n>=0), R^(-n) g^e (n<0).

    Return coefficient sign, power of central f, normal word. This uses
    PR=RP=f and gP=-Pg,gR=-Rg,g^2=1.
    """
    n, e = a
    m, h = b
    sign = -1 if (e * m) % 2 else 1
    fpower = min(abs(n), abs(m)) if n * m < 0 else 0
    return sign, fpower, (n + m, (e + h) % 2)


def normal_form_checks():
    words = [(n, e) for n in range(-3, 4) for e in range(2)]
    for a in words:
        for b in words:
            for c in words:
                sab, fab, ab = product(a, b)
                sl, fl, left = product(ab, c)
                sbc, fbc, bc = product(b, c)
                sr, fr, right = product(a, bc)
                assert (sab * sl, fab + fl, left) == (sbc * sr, fbc + fr, right)
    assert product((1, 0), (-1, 0)) == (1, 1, (0, 0))
    assert product((-1, 0), (1, 0)) == (1, 1, (0, 0))
    assert product((0, 1), (1, 0)) == (-1, 0, (1, 1))
    basis = [(0, 0), (0, 1), (1, 0), (1, 1), (-1, 0), (-1, 1)]
    radical = basis[2:]

    def special_mul(a, b):
        out = {}
        for x, cx in a.items():
            for y, cy in b.items():
                sign, fpower, word = product(x, y)
                if fpower or abs(word[0]) >= 2:
                    continue
                out[word] = out.get(word, Fraction(0)) + sign * cx * cy
        return {word: val for word, val in out.items() if val}

    for a in radical:
        for b in radical:
            assert special_mul({a: Fraction(1)}, {b: Fraction(1)}) == {}
    ep = {(0, 0): Fraction(1, 2), (0, 1): Fraction(1, 2)}
    em = {(0, 0): Fraction(1, 2), (0, 1): Fraction(-1, 2)}
    assert special_mul(ep, ep) == ep
    assert special_mul(em, em) == em
    assert special_mul(ep, em) == {}
    dimensions = []
    for left in (ep, em):
        row = []
        for right in (ep, em):
            columns = []
            for w in basis:
                p = special_mul(special_mul(left, {w: Fraction(1)}), right)
                columns.append([sp.Rational(p.get(k, 0)) for k in basis])
            row.append(sp.Matrix.hstack(*(sp.Matrix(col) for col in columns)).rank())
        dimensions.append(row)
    assert dimensions == [[1, 2], [2, 1]]
    return {"normal_form_associativity_cases": len(words) ** 3,
            "special_fiber_dimension": len(basis), "radical_dimension": len(radical),
            "radical_square_zero": True, "corner_dimensions": dimensions,
            "simple_dimensions": [1, 1]}


def result():
    return {"schema": "vk_endpoint_McKay_v38_exact_v1", "status": "PASS",
            "universal_symbolic": symbolic_checks(), "cyclotomic_half_norms": half_norm_checks(),
            "skew_group_normal_form": normal_form_checks(),
            "all_order_proof": "GWA direct sum + full idempotent + implicit function theorem; finite cases only verify implementation"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    actual = result()
    if args.check:
        expected = json.loads(args.check.read_text(encoding="utf-8"))
        assert actual == expected
        print(json.dumps({"status": "PASS", "certificate": str(args.check),
                          "sha256": hashlib.sha256(args.check.read_bytes()).hexdigest()}, sort_keys=True))
    else:
        print(json.dumps(actual, ensure_ascii=False, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
