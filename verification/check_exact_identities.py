#!/usr/bin/env python3
"""Finite exact-arithmetic diagnostics, not a proof of the general theorem.

Only the Python standard library is used. The two moment implementations
start from different expressions: an orthant volume polynomial and a
binomial-mixture finite product. All checked values are rational.
"""

from fractions import Fraction as Q
from math import comb, factorial, prod
from pathlib import Path
import json


def harmonic(k):
    return sum((Q(1, i) for i in range(1, k + 1)), Q(0))


def beta_integer_second(x, length):
    """Integral_0^1 t^(x-1) (1-t)^length dt, for rational x > 0."""
    return Q(factorial(length)) / prod(x + j for j in range(length + 1))


def layer_moment(m, a, b, p):
    """Scaled-simplex L^p moment, from the orthant level polynomial.

    p is an integer here, so powers of the rational scales stay rational.
    """
    z = sum(
        Q(comb(m, k) ** 2 * comb(k, j))
        * (a - b) ** j
        * b ** (m * p + m - j)
        * beta_integer_second(Q(m * p), m - j)
        for k in range(m + 1)
        for j in range(k + 1)
    )
    return (Q(factorial(m)) / (a * b) ** m) ** p * Q(m * p, factorial(m)) * z


def mixture_moment(m, a, b, p):
    q = 1 - b / a
    z = sum(
        Q(comb(m, j)) * q**j * (1 - q) ** (m - j)
        * prod(Q(m + ell, m * p + ell) for ell in range(1, m - j + 1))
        for j in range(m + 1)
    )
    return (Q(factorial(m)) / a**m) ** (p - 1) * z


def layer_entropy_correction(m, a, b):
    """Entropy minus [-log(m!) + m log(a)], from differentiated layers.

    The log(b) and scale prefactors cancel. The remaining derivative
    of p*B(mp,L+1) is a rational harmonic sum at p=1.
    """
    correction = Q(0)
    for k in range(m + 1):
        for j in range(k + 1):
            length = m - j
            mass = (
                Q(factorial(m)) / (a * b) ** m
                * Q(m, factorial(m))
                * Q(comb(m, k) ** 2 * comb(k, j))
                * (a - b) ** j * b ** (2 * m - j)
                * beta_integer_second(Q(m), length)
            )
            correction += mass * m * (harmonic(2 * m - j) - harmonic(m))
    return correction


def run():
    counts = {
        "vandermonde": 0,
        "layer_vs_mixture_moments": 0,
        "normalization": 0,
        "entropy_derivative": 0,
        "harmonic_bound": 0,
        "binomial_moments": 0,
        "F_increment": 0,
    }
    for m in range(1, 21):
        for j in range(m + 1):
            assert sum(comb(m, k) ** 2 * comb(k, j) for k in range(j, m + 1)) == (
                comb(m, j) * comb(2 * m - j, m)
            )
            counts["vandermonde"] += 1

    scales = [(Q(1), Q(1)), (Q(2), Q(1)), (Q(7, 3), Q(4, 5)), (Q(13, 7), Q(12, 7))]
    for m in range(1, 13):
        for a, b in scales:
            for p in range(1, 5):
                lhs, rhs = layer_moment(m, a, b, p), mixture_moment(m, a, b, p)
                assert lhs == rhs, (m, a, b, p, lhs, rhs)
                counts["layer_vs_mixture_moments"] += 1
                if p == 1:
                    assert lhs == 1
                    counts["normalization"] += 1
            q = 1 - b / a
            expected = m * sum(
                Q(comb(m, j)) * q**j * (1 - q) ** (m - j)
                * (harmonic(2 * m - j) - harmonic(m))
                for j in range(m + 1)
            )
            assert layer_entropy_correction(m, a, b) == expected
            counts["entropy_derivative"] += 1

    for m in range(1, 101):
        for j in range(m + 1):
            assert harmonic(2 * m) - harmonic(2 * m - j) <= (
                Q(j, 2 * m) + Q(j * (j - 1), 4 * m * m)
            )
            counts["harmonic_bound"] += 1

    for m in range(1, 41):
        for q in [Q(0), Q(1, 10), Q(1, 3), Q(1, 2), Q(9, 10), Q(1)]:
            weights = [Q(comb(m, j)) * q**j * (1 - q) ** (m - j) for j in range(m + 1)]
            assert sum(weights) == 1
            assert sum(j * weights[j] for j in range(m + 1)) == m * q
            assert sum(j * (j - 1) * weights[j] for j in range(m + 1)) == m * (m - 1) * q**2
            counts["binomial_moments"] += 1

    def F(k):
        return k * (harmonic(2 * k) - harmonic(k))

    for k in range(1, 101):
        assert F(k + 1) - F(k) == harmonic(2 * k) - harmonic(k) + Q(1, 2 * (2 * k + 1))
        counts["F_increment"] += 1

    report = {
        "status": "PASS",
        "arithmetic": "Python integers and fractions.Fraction only",
        "counts": counts,
        "total_checked_instances": sum(counts.values()),
        "scope": "Finite diagnostics only. General statements are proved in the manuscript; no Lean verification is claimed.",
    }
    destination = Path(__file__).with_name("results.json")
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    run()
