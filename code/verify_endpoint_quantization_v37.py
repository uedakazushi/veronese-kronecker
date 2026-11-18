#!/usr/bin/env python3
"""Exact checks for the endpoint Ore family (v37).

Requires SymPy.  Normal invocation prints deterministic JSON and writes no file.
Use --check CERTIFICATE to recompute and compare with a previously saved JSON.
The all-weight statements are proved in the companion TeX; finite H/CGG cases
below are implementation checks, not an extrapolation to arbitrary m.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from pathlib import Path

import sympy as sp


class PBW3:
    """Normal forms in B_{gamma,s}; words use 0=x, 1=y, 2=Z."""

    def __init__(self, gamma, s, symbolic=False):
        self.g, self.s = gamma, s
        self.symbolic = symbolic
        self.one = sp.Integer(1) if symbolic else Fraction(1)
        self.D = self.one - gamma * s * s
        assert self.D != 0
        self.a, self.b = s * s / self.D, s / self.D
        self.c = (self.one + gamma * s * s) / self.D
        a, b, c, g = self.a, self.b, self.c, gamma
        self.rules = {
            (1, 0): {(0, 1): c, (0, 0): -b, (0, 2): -2 * g * b},
            (2, 0): {(0, 2): c, (0, 1): -2 * b, (0, 0): a},
            (2, 1): {(1, 2): self.one, (0, 1): a, (0, 2): -b},
        }
        self.rules = {w: self.clean(p) for w, p in self.rules.items()}
        self.gens = [{(i,): self.one} for i in range(3)]
        self.x, self.y, self.z = self.gens
        self.sigma_images = [
            self.x,
            self.add(self.scale(c, self.y), self.scale(-b, self.x),
                     self.scale(-2 * g * b, self.z)),
            self.add(self.scale(c, self.z), self.scale(-2 * b, self.y),
                     self.scale(a, self.x)),
        ]
        self.Q = self.add(
            self.scale(self.one / self.D, self.mul(self.x, self.z)),
            self.scale(-s / self.D, self.mul(self.x, self.y)),
            self.scale(-self.one, self.mul(self.y, self.y)),
            self.scale(g, self.mul(self.z, self.z)),
        )

    def clean(self, p):
        result = {}
        for w, a in p.items():
            a = sp.cancel(a) if self.symbolic else a
            if a:
                result[w] = a
        return result

    def add(self, *ps):
        out = {}
        for p in ps:
            for w, a in p.items():
                out[w] = out.get(w, 0) + a
        return self.clean(out)

    def scale(self, a, p):
        return self.clean({w: a * b for w, b in p.items()})

    def neg(self, p):
        return self.scale(-self.one, p)

    @lru_cache(None)
    def nf(self, w):
        for i in range(len(w) - 1):
            if w[i:i + 2] in self.rules:
                return self.add(*(
                    self.scale(a, self.nf(w[:i] + u + w[i + 2:]))
                    for u, a in self.rules[w[i:i + 2]].items()
                ))
        return {w: self.one}

    def mul(self, p, q):
        return self.add(*(
            self.scale(a * b, self.nf(w + u))
            for w, a in p.items() for u, b in q.items()
        ))

    def comm(self, p, q):
        return self.add(self.mul(p, q), self.neg(self.mul(q, p)))

    def power(self, p, n):
        ans = {(): self.one}
        for _ in range(n):
            ans = self.mul(ans, p)
        return ans

    def substitute(self, p, images):
        terms = []
        for w, a in p.items():
            term = {(): a}
            for letter in w:
                term = self.mul(term, images[letter])
            terms.append(term)
        return self.add(*terms)

    def sigma(self, p):
        return self.substitute(p, self.sigma_images)

    def divide_left_x(self, p):
        assert all(w and w[0] == 0 for w in p), "not left divisible by x"
        return {w[1:]: a for w, a in p.items()}

    def delta(self, H, p):
        return self.divide_left_x(self.comm(p, H))

    def relation_polynomials(self):
        return [self.add({w: self.one}, self.neg(p))
                for w, p in self.rules.items()]


def universal_checks():
    g, s = sp.symbols("gamma s")
    B = PBW3(g, s, symbolic=True)
    x, y, z = B.gens
    left = B.add(*(
        B.scale(a, B.nf(w + (0,))) for w, a in B.rules[(2, 1)].items()
    ))
    right = B.add(*(
        B.scale(a, B.nf((2,) + w)) for w, a in B.rules[(1, 0)].items()
    ))
    assert not B.add(left, B.neg(right))
    for generator, sigma in zip(B.gens, B.sigma_images):
        assert not B.add(B.mul(generator, x), B.neg(B.mul(x, sigma)))
        assert not B.comm(B.Q, generator)
    for relation in B.relation_polynomials():
        assert not B.substitute(relation, B.sigma_images)
    assert not B.add(B.sigma(B.Q), B.neg(B.Q))
    inverse_images = [
        {w: sp.cancel(a.subs(s, -s)) for w, a in p.items()}
        for p in B.sigma_images
    ]
    for i in range(3):
        assert not B.add(B.substitute(inverse_images[i], B.sigma_images),
                         B.neg(B.gens[i]))
        assert not B.add(B.substitute(B.sigma_images[i], inverse_images),
                         B.neg(B.gens[i]))
    assert sp.cancel(B.c ** 2 - 4 * g * B.b ** 2 - 1) == 0
    assert sp.cancel(B.c - 1 - 2 * g * B.a) == 0
    assert sp.cancel(B.a * (B.c + 1) - 2 * B.b ** 2) == 0

    rho = sp.symbols("rho", nonzero=True)
    t = (1 - s * rho) / (1 + s * rho)
    k = (1 / t - t) / (4 * rho * rho)
    u = B.add(y, B.scale(rho, z), B.scale(1 / (2 * rho), x))
    v = B.add(y, B.scale(-rho, z), B.scale(-1 / (2 * rho), x))

    def after_sqrt_zero(p):
        return all(sp.cancel(a.subs(g, rho * rho)) == 0 for a in p.values())

    assert after_sqrt_zero(B.add(B.mul(u, x), B.scale(-t, B.mul(x, u))))
    assert after_sqrt_zero(B.add(B.mul(v, x), B.scale(-1 / t, B.mul(x, v))))
    assert after_sqrt_zero(B.add(B.comm(u, v), B.scale(-k, B.mul(x, x))))
    assert after_sqrt_zero(B.add(B.Q, B.mul(u, v),
                                B.scale(t / (4 * rho * rho), B.mul(x, x))))
    assert after_sqrt_zero(B.add(B.sigma(u), B.scale(-t, u)))
    assert after_sqrt_zero(B.add(B.sigma(v), B.scale(-1 / t, v)))

    # Explicit isomorphism from (gamma,s) to (s^2 gamma,1).
    T = PBW3(s * s * g, sp.Integer(1), symbolic=True)
    images = [T.x, T.scale(s, T.y), T.scale(s * s, T.z)]
    for relation in B.relation_polynomials():
        assert not T.substitute(relation, images)
    for i in range(3):
        assert not T.add(T.substitute(B.sigma_images[i], images),
                         T.neg(T.sigma(images[i])))
    assert not T.add(T.substitute(B.Q, images), T.scale(-s * s, T.Q))
    # A source y^(n-k) Z^k acquires the weight s^(n+k).
    n, k_index = sp.symbols("n k", integer=True, nonnegative=True)
    assert sp.expand((n - k_index) + 2 * k_index - n - k_index) == 0

    return {
        "coefficient_field": "Q(gamma,s)",
        "only_critical_word": "Zyx",
        "diamond_overlap": True,
        "normal_regular_x_from_PBW": True,
        "sigma_preserves_all_relations": True,
        "sigma_inverse_s_to_minus_s": True,
        "central_Q_and_sigma_fixed_Q": True,
        "diagonal_Ore_change_over_gamma_equals_rho_squared": True,
        "family_scaling_gamma_weight_2_H_k_weight_k": True,
    }


def finite_H_checks():
    cases = []
    # The universal Ore argument handles every weight; one full binary quintic
    # at two exact coefficient values is enough to exercise the implementation.
    for m in (4,):
        n = m + 1
        for g, s in ((Fraction(0), Fraction(1)),
                     (Fraction(1, 4), Fraction(1))):
            B = PBW3(g, s)
            check_count = 0
            for k in range(n + 1):
                H = {(1,) * (n - k) + (2,) * k: Fraction(1)}
                delta = lambda p: B.delta(H, p)
                for u in B.gens:
                    # Construction of delta must divide a genuine PBW left ideal.
                    d = delta(u)
                    assert not B.add(B.mul(B.x, d), B.neg(B.comm(u, H)))
                    for v in B.gens:
                        rhs = B.add(B.mul(B.sigma(u), delta(v)),
                                    B.mul(delta(u), v))
                        assert not B.add(delta(B.mul(u, v)), B.neg(rhs))
                        check_count += 1
                assert not B.add(delta(B.x), B.neg(H), B.sigma(H))
                assert not delta(H)
                assert not delta(B.Q)
                # These four identities are the coefficients of [xw+H,u]
                # for u=x,y,Z,w in the Ore basis.
                for u in B.gens:
                    assert not B.add(B.mul(B.x, delta(u)),
                                     B.mul(H, u), B.neg(B.mul(u, H)))
                assert not B.add(delta(B.x), B.sigma(H), B.neg(H))
            cases.append({
                "m": m, "gamma": str(g), "s": str(s),
                "binary_H_monomials": n + 1,
                "sigma_Leibniz_generator_pair_checks": check_count,
                "left_division_and_central_J_Q": True,
            })
            B.nf.cache_clear()
    return cases


def cgg_specialization_checks():
    xc, yc, zc, wc = sp.symbols("x y z w")
    q = xc * zc - yc * yc
    cases = []
    for j in (2, 3, 4):
        m, n = 2 * j, 2 * j + 1
        s = sp.Rational(1)
        Nj = lambda f: sp.expand(
            xc * sp.diff(f, yc) + 2 * yc * sp.diff(f, zc)
            - q ** j * sp.diff(f, wc)
        )
        X = lambda f: sp.expand(
            -xc * sp.diff(f, xc) + zc * sp.diff(f, zc)
            + wc * sp.diff(f, wc)
        )

        def star(f, g):
            left, right, result, k = sp.expand(f), sp.expand(g), 0, 0
            while left != 0:
                result += s ** k * left * right
                k += 1
                left = Nj(left)
                right = sp.expand((X(right) - (k - 1) * right) / k)
            return sp.expand(result)

        Zc = zc + s * yc
        assert sp.expand(star(yc, xc) - star(xc, yc) + s * xc ** 2) == 0
        assert sp.expand(star(Zc, xc) - star(xc, Zc)
                         + 2 * s * star(xc, yc) - s ** 2 * xc ** 2) == 0
        assert sp.expand(star(Zc, yc) - star(yc, Zc)
                         - s ** 2 * star(xc, yc) + s * star(xc, Zc)) == 0
        assert sp.expand(star(xc, Zc) - s * star(xc, yc)
                         - star(yc, yc) - q) == 0
        assert sp.expand(star(wc, xc) - star(xc, wc) - s * xc * q ** j) == 0
        assert sp.expand(star(wc, yc) - star(yc - s * xc, wc)) == 0
        assert sp.expand(star(wc, Zc)
                         - star(Zc - 2 * s * yc + s ** 2 * xc, wc)
                         + s * star(q ** j, Zc - s * yc)) == 0

        B = PBW3(Fraction(0), Fraction(1))
        Hstar = B.mul(B.power(B.Q, j), B.y)
        Hbinary = B.scale(Fraction((-1) ** j), B.power(B.y, n))
        G = B.divide_left_x(B.add(Hstar, B.neg(Hbinary)))
        assert not B.add(B.mul(B.x, G), Hbinary, B.neg(Hstar))
        Gsum = {}
        for ell in range(j):
            term = B.mul(B.power(B.Q, j - 1 - ell),
                         B.power(B.add(B.y, B.neg(B.x)), 2 * ell))
            term = B.mul(B.mul(term, B.add(B.z, B.neg(B.y))), B.y)
            Gsum = B.add(Gsum, B.scale(Fraction((-1) ** ell), term))
        assert not B.add(G, B.neg(Gsum))
        for u in B.gens:
            change_delta = B.add(B.delta(Hstar, u), B.neg(B.delta(Hbinary, u)))
            target = B.add(B.mul(B.sigma(u), G), B.neg(B.mul(G, u)))
            assert not B.add(change_delta, B.neg(target))
        cases.append({
            "m": m, "j": j, "s": "1", "alpha": "-1",
            "CGG_star_relations_checked_directly": 7,
            "Z_equals_z_plus_s_y": True,
            "binary_normalization_w_shift_checked": True,
            "G_finite_sum_equals_left_quotient": True,
            "G_PBW_terms": len(G),
        })
        B.nf.cache_clear()
    return cases


def semiclassical_checks():
    x, y, z, w, g = sp.symbols("x y Z w gamma")
    variables = [x, y, z, w]
    q = x * z - y * y + g * z * z
    # An arbitrary sample H with all binary monomials (m=4).
    coeffs = sp.symbols("h1:6")
    H = y ** 5 + sum(coeffs[k - 1] * y ** (5 - k) * z ** k
                     for k in range(1, 6))
    F = x * w + H
    PB = sp.zeros(4)
    # epsilon_{i j k l} q_k F_l gives the contraction convention in TeX.
    for i in range(4):
        for j in range(4):
            PB[i, j] = sp.expand(sum(
                sp.LeviCivita(i, j, k, ell) *
                sp.diff(q, variables[k]) * sp.diff(F, variables[ell])
                for k in range(4) for ell in range(4)
            ))
    assert sp.expand(PB[0, 1] - x * (x + 2 * g * z)) == 0
    assert sp.expand(PB[1, 2] - x * z) == 0
    assert sp.expand(PB[2, 0] + 2 * x * y) == 0
    for casimir in (q, F):
        gradient = sp.Matrix([sp.diff(casimir, v) for v in variables])
        assert all(sp.expand(p) == 0 for p in PB * gradient)
    for i in range(3):
        # [w,u]/s = sigma_1(u) w + {u,H}_B/x.
        sigma1 = [0, -x - 2 * g * z, -2 * y][i]
        correction = sum(PB[i, k] * sp.diff(H, variables[k]) for k in range(3))
        assert sp.expand(x * (PB[3, i] - sigma1 * w) - correction) == 0
    return {
        "sample_m": 4,
        "independent_binary_H_coefficients": 5,
        "Jacobian_contraction_sign": "i_Pi(Omega)=dq_gamma wedge dF",
        "base_brackets_and_Ore_first_order": True,
        "Casimirs_q_gamma_and_xw_plus_H": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path,
                        help="read-only comparison to an existing certificate")
    args = parser.parse_args()
    report = {
        "schema": "vk.endpoint_ore_quantization.v37",
        "status": "PASS",
        "universal_symbolic": universal_checks(),
        "finite_H_cases": finite_H_checks(),
        "CGG_specializations": cgg_specialization_checks(),
        "semiclassical": semiclassical_checks(),
        "scope": {
            "all_m_proof": "structural Ore/CY and KS arguments in companion TeX",
            "finite_tests_do_not_prove_all_m": True,
            "AS_regularity_CY_and_miniversality_are_not_claimed_as_computer_tests": True,
            "normal_invocation_writes_files": False,
        },
    }
    if args.check:
        expected = json.loads(args.check.read_text(encoding="utf-8"))
        if expected != report:
            raise SystemExit("certificate mismatch")
    print(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
