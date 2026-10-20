#!/usr/bin/env python3
"""Independent exact recomputation of the conservative per-attempt endpoint."""
from fractions import Fraction
from math import isqrt
from pathlib import Path
import json

threshold = Fraction(1, 2**100)
fixed = Fraction(495, 2**109) + Fraction(1, 2**126) + Fraction(1, 2**454)
r = (threshold - fixed) * 2**256 / 6
# Strict T*T < r means T*T <= floor((numerator-1)/denominator).
total = isqrt((r.numerator - 1) // r.denominator)
queries = total - 1161

def bound(q):
    return Fraction(6 * (q + 1161)**2, 2**256) + fixed

assert bound(queries) < threshold <= bound(queries + 1)
result = {
    'method': 'exact Fraction arithmetic and integer square root, strict inequality',
    'max_total_queries': total,
    'max_adversary_queries': queries,
    'bound_at_endpoint': str(bound(queries)),
    'bound_at_successor': str(bound(queries + 1)),
    'threshold': str(threshold),
}
assert result == json.loads((Path(__file__).parent / 'numeric-endpoint.json').read_text())
print(queries)
