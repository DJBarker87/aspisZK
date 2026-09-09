#!/usr/bin/env python3
"""Exact arithmetic control for the restricted rational-fold screen.

This does not certify applicability of the proposed causal composition.
"""
from fractions import Fraction
from math import comb, log2
import json

P = (1 << 31) - 1
K = P**4
T = 262_144
Q = 22
MATCH_CAP = 259

query = Fraction(comb(MATCH_CAP, Q), comb(T, Q))
conditional_screen = Fraction(3, K) + Fraction(Q, K - 1) + Fraction(18, K) + query

assert MATCH_CAP == 257 + 2
assert query < Fraction(1, 2**220)
assert conditional_screen < Fraction(1, 2**118)

print(json.dumps({
    "status": "arithmetic_verified_theorem_applicability_unresolved",
    "field_cardinality": K,
    "domain_fibres": T,
    "queries": Q,
    "nonpole_match_cap": 257,
    "pole_cap": 2,
    "possible_match_cap": MATCH_CAP,
    "query_term": {"numerator": query.numerator, "denominator": query.denominator,
                   "bits": -log2(float(query))},
    "conditional_screen": {
        "formula": "3/k + 22/(k-1) + 18/k + choose(259,22)/choose(262144,22)",
        "numerator": conditional_screen.numerator,
        "denominator": conditional_screen.denominator,
        "bits": -log2(float(conditional_screen)),
        "applicability": False,
    },
    "missing": [
        "four exact cleared folds imply correct OOD data or a recovered quotient",
        "selected final-domain index map to the proved affine coordinates",
        "causal game composition and source/transcript refinement",
        "individual component claim binding and checked witness extraction",
    ],
}, indent=2, sort_keys=True))
