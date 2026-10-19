#!/usr/bin/env python3
"""Exact tail of the per-transaction PDA search cost (option A).
Each canonical search succeeds on attempt k with P = 2^-k (k = 1..255, the
residual 2^-255 mass is the 'no bump' failure) - fact F4 of the study.
Extra cost over one attempt = 1500 (k-1) CU (fact F1). The two marker
searches have the same seeds, hence the same k. Prints JSON."""
import json, sys
from fractions import Fraction as F
from math import log2
CU = 1500
def geo():  # distribution of extra attempts e = k-1, e in 0..254
    return {e: F(1, 2 ** (e + 1)) for e in range(255)}
def conv(a, b):
    out = {}
    for x, px in a.items():
        for y, py in b.items():
            out[x + y] = out.get(x + y, 0) + px * py
    return out
def scale(a, s):
    return {s * x: p for x, p in a.items()}
def tail(dist, threshold_extra_attempts):
    return sum(p for x, p in dist.items() if x > threshold_extra_attempts)
# base settlement CU (no extra attempts on the remaining per-transaction searches):
# swept random maxima from cu-bound-20261019 (upper bounds: they already contain
# whatever extra attempts those runs drew) minus the measured Part-2 saving.
SAVED = 4123
bases = {'transfer': 1192252 - SAVED, 'withdrawal': 1206877 - SAVED}
scenarios = {
    # name: (searches with independent seeds, marker multiplicity)
    'current: checkpoint+page+marker x2': (2, 2),
    'current rollover: checkpoint+page+next page+marker x2': (3, 2),
    'marker searched once': (2, 1),
    'marker once, checkpoint stored bump': (1, 1),
    'marker only (x1)': (0, 1),
}
res = {}
for name, (indep, mult) in scenarios.items():
    d = scale(geo(), mult)
    for _ in range(indep):
        d = conv(d, geo())
    row = {}
    for kind, base in bases.items():
        for limit in (1300000, 1400000):
            thr = (limit - base) // CU  # extra attempts allowed
            p = tail(d, thr)
            row[f'{kind}@{limit}'] = {'base': base, 'max_extra_attempts': thr,
                                      'p_exceed': float(p), 'log2_p': (log2(p) if p > 0 else None)}
    res[name] = row
json.dump(res, sys.stdout, indent=1)
print()
