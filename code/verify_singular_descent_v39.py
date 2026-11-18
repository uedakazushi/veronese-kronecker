#!/usr/bin/env python3
"""Exact regression checks for the v39 singular-locus descent theorem.

All arithmetic is in Q[t]/Phi_ell(t), and in the six-dimensional square-zero
extension L + L_sigma p + L_sigma r, with kappa^2=-t Q/beta.  These finite
checks do not replace the all-order proof in singular_descent_ja_v39.tex.
No numerical approximations and no external CAS executable are used.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from pathlib import Path


def divide_monic_exact(a, b):
    a = list(a)
    quotient = [0] * (len(a) - len(b) + 1)
    for i in range(len(a) - len(b), -1, -1):
        coefficient = a[i + len(b) - 1]
        quotient[i] = coefficient
        for j, value in enumerate(b):
            a[i + j] -= coefficient * value
    assert not any(a), "nonexact cyclotomic polynomial division"
    return tuple(quotient)


@lru_cache(maxsize=None)
def cyclotomic_polynomial(n):
    coefficients = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            coefficients = divide_monic_exact(coefficients, cyclotomic_polynomial(d))
    return tuple(coefficients)


class Cyclotomic:
    def __init__(self, ell: int):
        self.ell = ell
        self.mod = [Fraction(c) for c in cyclotomic_polynomial(ell)]
        self.n = len(self.mod) - 1
        self.zero = (Fraction(0),) * self.n
        self.one = self.scalar(1)
        self.t = self.reduce([0, 1])
        self.powers = [self.one]
        for _ in range(1, ell):
            self.powers.append(self.mul(self.powers[-1], self.t))
        assert self.mul(self.powers[-1], self.t) == self.one

    def scalar(self, x):
        return (Fraction(x),) + (Fraction(0),) * (self.n - 1)

    def reduce(self, a):
        a = [Fraction(x) for x in a]
        a += [Fraction(0)] * max(0, self.n - len(a))
        for k in range(len(a) - 1, self.n - 1, -1):
            c = a[k]
            if c:
                for j in range(self.n):
                    a[k - self.n + j] -= c * self.mod[j]
        return tuple(a[:self.n])

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def neg(self, a):
        return tuple(-x for x in a)

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def scale(self, a, c):
        return tuple(Fraction(c) * x for x in a)

    def mul(self, a, b):
        if a == self.zero or b == self.zero:
            return self.zero
        if a == self.one:
            return b
        if b == self.one:
            return a
        out = [Fraction(0)] * (2 * self.n - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        out[i + j] += x * y
        return self.reduce(out)

    def tp(self, k):
        return self.powers[k % self.ell]


class RadicalAlgebra:
    # index 2*s+a denotes kappa^a times 1, p, or r according to s=0,1,2.
    def __init__(self, field, q, beta):
        self.f = field
        self.kappa_square = field.scale(field.t, -Fraction(q, beta))
        self.zero = {}
        self.one = {0: field.one}
        self.basis = [{i: field.one} for i in range(6)]

    def scalar(self, x):
        return {} if x == self.f.zero else {0: x}

    def add(self, a, b):
        out = dict(a)
        for i, x in b.items():
            val = self.f.add(out.get(i, self.f.zero), x)
            if val == self.f.zero:
                out.pop(i, None)
            else:
                out[i] = val
        return out

    def scale(self, a, x):
        return {i: v for i, c in a.items() if (v := self.f.mul(c, x)) != self.f.zero}

    def mul(self, a, b):
        out = {}
        for i, x in a.items():
            s, ea = divmod(i, 2)
            for j, y in b.items():
                t, eb = divmod(j, 2)
                if s and t:
                    continue
                coeff = self.f.mul(x, y)
                if s and eb:
                    coeff = self.f.neg(coeff)
                exponent = ea + eb
                if exponent == 2:
                    coeff = self.f.mul(coeff, self.kappa_square)
                    exponent = 0
                index = 2 * (s or t) + exponent
                out = self.add(out, {index: coeff})
        return out


class Matrices:
    def __init__(self, ring, d):
        self.r = ring
        self.f = ring.f
        self.d = d
        self.I = {(i, i): ring.one for i in range(d)}

    def elementary(self, i, j, value=None):
        if value is None:
            value = self.r.one
        return {} if not value else {(i, j): value}

    def diagonal(self, value):
        return {(i, i): value for i in range(self.d)} if value else {}

    def add(self, a, b):
        out = dict(a)
        for ij, c in b.items():
            val = self.r.add(out.get(ij, {}), c)
            if val:
                out[ij] = val
            else:
                out.pop(ij, None)
        return out

    def scale(self, a, c):
        return {ij: v for ij, x in a.items() if (v := self.r.scale(x, c))}

    def mul(self, a, b):
        out = {}
        for (i, j), x in a.items():
            for (k, l), y in b.items():
                if j == k:
                    val = self.r.mul(x, y)
                    if val:
                        out = self.add(out, {(i, l): val})
        return out

    def power(self, a, n):
        out = self.I
        while n:
            if n & 1:
                out = self.mul(out, a)
            a = self.mul(a, a)
            n >>= 1
        return out


def verify_case(ell, q, beta):
    d = ell // 2
    f = Cyclotomic(ell)
    r = RadicalAlgebra(f, q, beta)
    m = Matrices(r, d)
    one, kappa, p, _, rr, _ = r.basis
    zero = {}
    checks = 0

    def check(left, right, label):
        nonlocal checks
        assert left == right, (ell, q, beta, label, left, right)
        checks += 1

    for a in r.basis:
        for b in r.basis:
            for c in r.basis:
                check(r.mul(r.mul(a, b), c), r.mul(a, r.mul(b, c)), "corner associativity")

    ai = [f.scale(f.sub(f.tp(2*i), f.one), q) for i in range(d)]
    cd = Fraction((-1)**(d-1) * d * q**(d-1))
    product = f.one
    for a in ai[1:]:
        assert a != f.zero
        product = f.mul(product, a)
    check(product, f.scalar(cd), "internal edge product")

    x = {(i, i): r.scale(kappa, f.tp(i)) for i in range(d)}
    u = {(i-1, i): one for i in range(1, d)}
    u[(d-1, 0)] = p
    v = {(i, i-1): r.scalar(ai[i]) for i in range(1, d)}
    v[(0, d-1)] = r.scale(rr, f.scalar(1 / cd))

    x2 = m.power(x, 2)
    check(m.mul(u, x), m.scale(m.mul(x, u), f.t), "ux=t xu")
    check(m.mul(v, x), m.scale(m.mul(x, v), f.tp(-1)), "vx=t^-1 xv")
    check(m.mul(v, u), m.add(m.scale(m.I, f.scalar(-q)),
                            m.scale(x2, f.scale(f.tp(-1), -beta))), "vu norm")
    check(m.mul(u, v), m.add(m.scale(m.I, f.scalar(-q)),
                            m.scale(x2, f.scale(f.t, -beta))), "uv norm")
    xi = Fraction((-1)**(d+1)) * Fraction(q, beta)**d
    check(m.power(x, ell), m.scale(m.I, f.scalar(xi)), "Xi on Sigma")
    check(m.power(u, d), m.diagonal(p), "u^d=pI")
    check(m.power(v, d), m.diagonal(rr), "v^d=rI")
    check(m.power(u, ell), zero, "U=0")
    check(m.power(v, ell), zero, "V=0")
    check(m.mul(m.power(u, d), m.power(v, d)), zero, "half norm zero")
    check(m.mul(m.power(v, d), m.power(u, d)), zero, "reverse half norm zero")

    z = m.scale(x2, f.scale(f.tp(-1), -Fraction(beta, q)))
    projectors = []
    for i in range(d):
        projector = {}
        for k in range(d):
            projector = m.add(projector, m.scale(m.power(z, k), f.scale(f.tp(-2*i*k), Fraction(1,d))))
        check(projector, m.elementary(i, i), "Fourier paired projector")
        projectors.append(projector)

    # Explicit matrix units obtained only from original generators and R-units.
    left = [projectors[0]]
    right = [projectors[0]]
    for i in range(1, d):
        inverse_ai = f.zero
        for k in range(1, d):
            inverse_ai = f.add(inverse_ai, f.scale(f.tp(2*i*k), Fraction(k, d*q)))
        check(f.mul(ai[i], inverse_ai), f.one, "unit inverse")
        forward = m.scale(m.mul(m.mul(projectors[i], v), projectors[i-1]), inverse_ai)
        backward = m.mul(m.mul(projectors[i-1], u), projectors[i])
        left.append(m.mul(forward, left[-1]))
        right.append(m.mul(right[-1], backward))
        check(left[-1], m.elementary(i, 0), "left matrix unit")
        check(right[-1], m.elementary(0, i), "right matrix unit")

    corner_generators = [projectors[0],
                         m.mul(m.mul(projectors[0], x), projectors[0]),
                         m.mul(m.mul(projectors[0], m.power(u,d)), projectors[0]),
                         None,
                         m.mul(m.mul(projectors[0], m.power(v,d)), projectors[0]),
                         None]
    corner_generators[3] = m.mul(corner_generators[1], corner_generators[2])
    corner_generators[5] = m.mul(corner_generators[1], corner_generators[4])
    for k, b in enumerate(r.basis):
        check(corner_generators[k], m.elementary(0, 0, b), "corner basis recovery")
        for i in range(d):
            for j in range(d):
                check(m.mul(m.mul(left[i], corner_generators[k]), right[j]),
                      m.elementary(i, j, b), "full 6d^2 basis recovery")

    trace_sum = f.zero
    for i in range(d):
        trace_sum = f.add(trace_sum, f.tp(i))
    check(f.mul(f.sub(f.one, f.t), trace_sum), f.scalar(2), "simple trace coordinate")
    return {"ell": ell, "d": d, "Q": q, "beta": beta,
            "cyclotomic_degree": f.n, "corner_rank": 6,
            "singular_algebra_rank": 6*d*d, "radical_rank": 4*d*d,
            "simple_dimensions": [d,d], "exact_equalities": checks,
            "status": "PASS"}


def run():
    cases = [verify_case(ell, q, beta)
             for ell in range(4, 25, 2) for q, beta in [(1,1),(2,3)]]
    return {
        "schema": "vk.singular-descent.v39.1",
        "status": "PASS",
        "arithmetic": "exact rational arithmetic in Q[t]/Phi_ell(t)",
        "scope": "finite regression checks; the TeX proof treats all even ell>=4 and all nonzero Q,beta",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "orders": list(range(4,25,2)),
        "parameter_pairs": [[1,1],[2,3]],
        "cases": cases,
        "total_exact_equalities": sum(c["exact_equalities"] for c in cases),
        "not_computational_claims": [
            "connectedness of the double cover is proved by its Laurent polynomial coordinate ring",
            "Brauer period and index for all orders are proved by the cyclic norm argument",
            "global End-type obstruction follows from the nonzero generic Brauer class"
        ]
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = run()
    if args.check:
        saved = json.loads(args.check.read_text())
        assert saved == result, "certificate differs from exact recomputation"
        print(json.dumps({"status":"PASS", "certificate":str(args.check),
                          "certificate_sha256":hashlib.sha256(args.check.read_bytes()).hexdigest(),
                          "total_exact_equalities":result["total_exact_equalities"]}, sort_keys=True))
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
