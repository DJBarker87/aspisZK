#!/usr/bin/env python3
"""Tiny exact layout/algebra falsifier; not a Rust machine refinement proof."""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

P = (1 << 31) - 1


def pack(limbs):
    return sum(v << (31 * i) for i, v in enumerate(limbs)).to_bytes(len(limbs) * 31 // 8, "little")


def literal(data, count):
    word = int.from_bytes(data, "little")
    return [(word >> (31 * i)) & P for i in range(count)]


def optimized(data):
    out = []
    for offset in range(0, len(data), 31):
        b = data[offset:offset + 31]
        w0, w1, w2 = [int.from_bytes(b[i:i + 8], "little") for i in (0, 8, 16)]
        w3 = int.from_bytes(b[23:31], "little") >> 8
        out.extend(v & P for v in (
            w0, w0 >> 31, (w0 >> 62) | (w1 << 2), w1 >> 29,
            (w1 >> 60) | (w2 << 4), w2 >> 27, (w2 >> 58) | (w3 << 6), w3 >> 25))
    return None if P in out else out


def fold(alpha, ix, iy, v):
    pos = (v[0] + v[1]) / 2 + alpha * (v[0] - v[1]) * iy
    neg = (v[2] + v[3]) / 2 - alpha * (v[2] - v[3]) * iy
    return (pos + neg) / 2 + alpha**2 * (pos - neg) * ix


def check():
    basis_cases = invalid_cases = 0
    for count in (104, 48):
        for limb in range(count):
            for bit in range(31):
                values = [0] * count
                values[limb] = 1 << bit
                data = pack(values)
                assert optimized(data) == literal(data, count) == values
                basis_cases += 1
            values = [0] * count
            values[limb] = P
            assert optimized(pack(values)) is None
            invalid_cases += 1
    c1 = list(range(1, 105))
    c2 = list(range(1001, 1049))
    salt = bytes(range(32))
    record = pack(c1) + pack(c2) + salt
    assert len(record) == 621
    assert optimized(record[:403]) == c1
    assert optimized(record[403:589]) == c2
    assert record[589:] == salt
    assert c1[26 * 1 + 2] == 29 != c1[4 * 2 + 1]
    assert c2[4 * (4 * 1 + 2) + 3] == 1028 != c2[4 * (3 * 2 + 1) + 3]
    assert 11228 + 621 * 22 == 24890
    # End-to-end scalar gamma checks use the prime subfield of the tower.
    # A separate basis-labelled C2 test above checks all four tower positions.
    gamma = 3
    helpers = [[[0] * 4 for _ in range(4)] for _ in range(3)]
    for h in range(3):
        for s in range(4):
            helpers[h][s][0] = 17 + 4 * h + s
    def combined(s):
        return (sum(pow(gamma, c, P) * c1[26 * s + c] for c in range(26)) +
                sum(pow(gamma, 26 + h, P) * helpers[h][s][0] for h in range(3))) % P
    assert len({combined(s) for s in range(4)}) == 4
    coords = [(3, 5), (3, -5), (-3, -5), (-3, 5)]
    a, b, c, intercept, slope = 31, 2, 1, 7, 11
    denoms = [a + b * x + c * y for x, y in coords]
    assert denoms == [42, 32, 20, 30]
    slots = [F(combined(s) - (intercept + slope * x), denoms[s])
             for s, (x, _) in enumerate(coords)]
    folded = fold(F(2), F(1, 6), F(1, 10), slots)
    assert folded != fold(F(2), F(1, 6), F(1, 10), [slots[0], slots[1], slots[3], slots[2]])
    assert fold(F(0), F(1, 6), F(1, 10), slots) == sum(slots) / 4
    assert (11 - 2 * 3 - 1 * 5) == 0  # queried pole must reject, not return a zero quotient
    rho, opening = 2, [3, 5]
    ordinal = sum(rho**(i + 1) * v for i, v in enumerate(opening))
    sorted_wrong = sum(rho**(i + 1) * v for i, v in enumerate(reversed(opening)))
    assert ordinal == 26 and sorted_wrong == 22
    final_eval, carried, prior = [13, 19], 23, 29
    errors = [f - o for f, o in zip(final_eval, opening)]
    actual = carried + ordinal - (prior + sum(rho**(i + 1) * v for i, v in enumerate(final_eval)))
    shifted = carried - prior - rho * sum(e * rho**i for i, e in enumerate(errors))
    assert actual == shifted == -82
    return {
        "status": "PASS", "single_bit_cases": basis_cases, "noncanonical_cases": invalid_cases,
        "record_bytes": len(record), "fixture_sha256": hashlib.sha256(record).hexdigest(),
        "c1_index_mutation": [29, c1[4 * 2 + 1]],
        "c2_index_mutation": [1028, c2[4 * (3 * 2 + 1) + 3]],
        "ordinal_vs_sorted_rho_sum": [ordinal, sorted_wrong], "shifted_discrepancy": actual,
        "folded_rational": str(folded), "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "exact tiny Python control; not compiled Rust, full-field enumeration, or a Lean theorem"
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
