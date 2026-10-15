#!/usr/bin/env python3
"""Enumerate current C1 eligibility supports under the fixed D18 permutation.

This is integer index bookkeeping only; it performs no field arithmetic or rank test.
Pinned source: ../privacy-wide/probe.rs SHA256
54ec15ab6aa9205d3a07d4de56680cd301b6fdfb769dd6281d17b2fb7a13b531
"""
import hashlib
import pathlib
import re
import ast

ROOT = pathlib.Path(__file__).resolve().parents[4]
SRC = ROOT / "docs/research/100bit-spend-path-20261013/privacy-wide/probe.rs"
EXPECTED = "54ec15ab6aa9205d3a07d4de56680cd301b6fdfb769dd6281d17b2fb7a13b531"
LOG = ROOT / "docs/research/100bit-spend-path-20261013/evidence/privacy-wide/wide-full-g0.log"
LOG_SHA256 = "d42d7fade8178f4de1b166b7eaeacf5904bc3b77a17ba42b5613c6eaee83a70b"
raw = SRC.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED, "probe.rs source pin changed"
s = raw.decode()
active_text = re.search(r"const ACTIVE: \[u16; 64\] = \[(.*?)\];", s, re.S).group(1)
ACTIVE = [int(x) for x in re.findall(r"\d+", active_text)]
assert len(ACTIVE) == 64
log_bytes = LOG.read_bytes()
assert hashlib.sha256(log_bytes).hexdigest() == LOG_SHA256, "historical log pin changed"
LOG_TEXT = log_bytes.decode()

def inactive(r):
    return ACTIVE[r // 16] & (1 << (r % 16)) == 0

def eligible(c, r):
    if r < 912:
        return r % 16 >= 13
    if r < 1008:
        return not any(
            (r == 912 + 16 * (l // 4) + 1 + 4 * (l % 4) and c <= 8)
            or r == 913 + 16 * (l // 4) + 1 + 4 * (l % 4)
            for l in range(24)
        )
    r -= 48
    return not (
        any(
            (r == (b := 864 + 16 * (l // 4) + 1 + 2 * (l % 4)) and c <= 8)
            or r == b + 1
            or (r == (b ^ 12) and c < 8)
            for l in range(21)
        )
        or any(
            (r == b or r == b + 1 or r == (b ^ 12)) and c <= 10
            for v in range(3)
            for b in [960 + 2 * v]
        )
        or (r == 966 and c < 3)
        or (r == 967 and c < 2)
        or (r == 969 and c <= 10)
        or (r == 970 and c < 10)
    )

def transport(r):
    digit = lambda d: (r >> (2 * d)) & 3
    return digit(3) + 4 * digit(4) + 16 * digit(2) + 64 * digit(0) + 256 * digit(1)

def runs(vals):
    vals = sorted(vals)
    if not vals:
        return []
    out, lo, hi = [], vals[0], vals[0]
    for x in vals[1:]:
        if x == hi + 1:
            hi = x
        else:
            out.append((lo, hi))
            lo = hi = x
    out.append((lo, hi))
    return out

# C1's independent-support construction excludes pivot row 1023 and, for
# inactive rows, subtracts that row. Supports before transport are row indices.
row_supports = {c: {r for r in range(1024) if r != 1023 and eligible(c, r)} for c in range(16)}
coeff_supports = {c: {transport(r) for r in rows} for c, rows in row_supports.items()}
assert transport(1023) == 1023
common_rows = set.intersection(*(row_supports[c] for c in range(16)))
common_coeffs = set.intersection(*(coeff_supports[c] for c in range(16)))
# Cross-check the independently recomputed transported supports against the
# retained Z5 diagnostic, which used these same source predicates.
for c in range(16):
    match = re.search(rf"^Z5_ELIGIBLE_IMAGES column={c} coefficients=(\[.*?\]) balance_pivot_coefficient=(\d+)$", LOG_TEXT, re.M)
    assert match is not None
    logged = set(ast.literal_eval(match.group(1)))
    assert logged == coeff_supports[c], f"historical coefficient set mismatch in column {c}"
    assert int(match.group(2)) == transport(1023) == 1023
print("source_sha256", EXPECTED)
print("historical_log_sha256", LOG_SHA256)
print("historical_Z5_supports_match", True)
print("pivot", {"row": 1023, "inactive": inactive(1023), "eligible_by_column": [eligible(c, 1023) for c in range(16)], "transported_coefficient": transport(1023), "in_C1_support": False})
print("common_rows_count", len(common_rows), "runs", runs(common_rows))
print("common_coefficients_count", len(common_coeffs), "runs", runs(common_coeffs))
for c in range(16):
    coeffs = coeff_supports[c]
    print(f"column={c} row_count={len(row_supports[c])} coefficient_count={len(coeffs)} coefficient_runs={runs(coeffs)}")
    for residue in range(4):
        quotients = {x // 4 for x in coeffs if x % 4 == residue}
        print(f"  residue={residue} quotient_count={len(quotients)} quotient_runs={runs(quotients)}")
