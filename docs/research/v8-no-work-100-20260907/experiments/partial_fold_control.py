#!/usr/bin/env python3
"""Exact tiny geometric control. No payment, FS, image or relation claim.

The fixed received word is specified before alpha. At each alpha we enumerate
ALL constant-code finals, then count fresh distinct queries. This is exhaustive
over that final-selection family, not over received words or compact responses.
"""
from collections import Counter
from fractions import Fraction
import json
import math
import sys
from pathlib import Path

P = 31
NODES = (1, 2, 3, 4)

def inv(x):
    assert x % P
    return pow(x, -1, P)

def poly(roots):
    out = [1]
    for root in roots:
        nxt = [0] * (len(out) + 1)
        for j, value in enumerate(out):
            nxt[j] = (nxt[j] - root * value) % P
            nxt[j+1] = (nxt[j+1] + value) % P
        out = nxt
    return tuple(out)

def eval_poly(coefficients, alpha):
    out = 0
    for coefficient in reversed(coefficients):
        out = (out * alpha + coefficient) % P
    return out

def slots(x, y):
    return tuple((xx % P, yy % P) for xx, yy in
                 ((x, y), (x, -y), (-x, -y), (-x, y)))

def evaluate(point, coefficients):
    a, b, c, d = coefficients
    return tuple((a + yy*b + xx*c + xx*yy*d) % P for xx, yy in slots(*point))

def fold(point, word, alpha):
    x, y = point
    a, b, c, d = word
    left = ((a+b)*inv(2) + alpha*(a-b)*inv(2*y)) % P
    right = ((c+d)*inv(2) - alpha*(c-d)*inv(2*y)) % P
    return ((left+right)*inv(2) + alpha*alpha*(left-right)*inv(2*x)) % P

def decode(point, word):
    x, y = point
    a, b, c, d = word
    return ((a+b+c+d)*inv(4) % P, (a-b-c+d)*inv(4*y) % P,
            (a+b-c-d)*inv(4*x) % P, (a-b+c-d)*inv(4*x*y) % P)

def rational(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}

def result():
    seen, points = set(), []
    for x in range(1, P):
        for y in range(1, P):
            if (x*x+y*y) % P != 1 or (x, y) in seen:
                continue
            points.append((x, y))
            seen.update(slots(x, y))
    assert len(points) == 7 and len(seen) == 28
    assert len({(2*x*x-1) % P for x, _ in points}) == 7
    coefficients = [poly(a for a in NODES if a != node) for node in NODES]
    coefficients += [(0, 0, 0, 0)] * 3
    received = [evaluate(point, c) for point, c in zip(points, coefficients)]
    for point, c, word in zip(points, coefficients, received):
        assert decode(point, word) == c
        for j in range(4):
            basis = tuple(int(i == j) for i in range(4))
            assert decode(point, evaluate(point, basis)) == basis
    # In the lift of the constant final code, a full codeword has the SAME
    # four decoded coefficients at every fibre. Invertibility makes the
    # exact nearest distance T - largest tuple multiplicity, without any
    # favourable target search or enumerating P^4 coefficient tuples.
    minimum_full_code_distance = len(points) - max(Counter(coefficients).values())
    assert minimum_full_code_distance == 4
    matches = []
    query_pass_counts = []
    q = 2
    for alpha in range(P):
        values = [fold(point, word, alpha) for point, word in zip(points, received)]
        assert values == [eval_poly(c, alpha) for c in coefficients]
        target_matches = [sum(v == final for v in values) for final in range(P)]
        best = max(target_matches)
        assert target_matches[0] == best  # One pre-alpha final is already optimal.
        matches.append(best)
        query_pass_counts.append(math.comb(best, q))
        if alpha in NODES:
            assert sum(v != 0 for v in values) == 1
            assert best == 6
    assert [a for a, count in enumerate(matches) if count >= 6] == list(NODES)
    assert Fraction(sum(query_pass_counts), P*math.comb(7,q)) == Fraction(P+16,7*P)
    supports = [{i for i, c in enumerate(coefficients) if eval_poly(c, a) == 0}
                for a in NODES]
    assert len(set.intersection(*supports)) == 3
    # Optimistic screen for the universal four-support route. For its far
    # premise to be nonempty, 4B < T. Even allowing the extremal B here,
    # the surviving matching cap is 3T/4, not the ~9556 needed at q22.
    k, T, Q = (2**31-1)**4, 262144, 22
    B = (T-1)//4
    M = T-B-1
    bound = Fraction(3, k) + Fraction(math.comb(M, Q), math.comb(T, Q))
    assert M == 196608 and Fraction(1, 2**10) < bound < Fraction(1, 2**9)
    return {
        "field": P, "points": points, "fixed_decoded_fibres": coefficients,
        "four_nodes": NODES, "per_node_bad_fibres": 1,
        "nearest_full_lift_distance": minimum_full_code_distance,
        "common_support_fibres": 3, "factor_four_attained": True,
        "all_alpha_final_pairs_checked": P*P, "local_inverse_basis_checks": 28,
        "adaptive_constant_final_matching_counts": matches,
        "fixed_zero_final_always_optimal": True,
        "tiny_q": q,
        "optimal_tiny_pointwise_probability": rational(Fraction(sum(query_pass_counts), P*math.comb(7, q))),
        "scope": "one fixed pre-alpha received quotient, all constant-code adaptive finals; no image/relation/payment or pre-OOD commitment strategy",
        "QM31_optimistic_four_support_screen": {
            "B": B, "matching_cap": M, "bound": rational(bound),
            "display_bits": math.log2(bound.denominator)-math.log2(bound.numerator),
            "status": "conditional geometric/query bound only; optimistic nonempty-radius ceiling cannot establish 100 bits",
        },
        "global_security_bound": None,
    }

if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        # Round-trip canonical JSON normalizes tuple/list representation.
        out = json.loads(json.dumps(out))
        assert json.loads(Path(__file__).with_name("partial-fold-control-output.json").read_text()) == out
        print("Exact sharp-four support control and conditional q22 arithmetic match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
