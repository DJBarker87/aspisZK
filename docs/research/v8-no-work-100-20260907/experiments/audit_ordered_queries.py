#!/usr/bin/env python3
"""Tiny exact order-sensitive checks; not a strategy search or QM31 certificate."""
import itertools
import json
import math
from collections import Counter
from fractions import Fraction


def first_distinct(tape, q):
    seen = []
    for value in tape:
        if len(seen) == q:
            break
        if value not in seen:
            seen.append(value)
    return tuple(seen) if len(seen) == q else None


def main():
    ordered_cases = 0
    for n in range(1, 8):
        for q in range(min(n, 3) + 1):
            schedules = list(itertools.permutations(range(n), q))
            for mask in range(1 << n):
                bad = {i for i in range(n) if mask >> i & 1}
                count = sum(all(i in bad for i in s) for s in schedules)
                assert Fraction(count, len(schedules)) == Fraction(
                    math.comb(len(bad), q), math.comb(n, q))
                ordered_cases += 1
    tapes = 0
    bounded_profiles = 0
    for n in range(1, 6):
        for length in range(1, 6):
            for q in range(1, min(n, length, 3) + 1):
                counts = Counter(first_distinct(tape, q)
                                 for tape in itertools.product(range(n), repeat=length))
                tapes += sum(counts.values())
                counts.pop(None, None)
                assert len(counts) == math.factorial(n) // math.factorial(n - q)
                assert len(set(counts.values())) == 1
                bounded_profiles += 1
    # Same set and same rho, different order: generic scalar acceptance is
    # not permutation invariant. This is a literal tiny-field batch check,
    # NOT a complete proof acceptance, strategy, attack or probability bound.
    p, rho = 7, 3
    def shifted(residual):
        return -sum(pow(rho, i+1, p)*r for i, r in enumerate(residual)) % p
    assert shifted((1, 2)) == 0
    assert shifted((2, 1)) == 6
    print(json.dumps({
        "scope": "exact reduced combinatorics and scalar-batch regression only",
        "ordered_matching_profiles": ordered_cases,
        "bounded_sampler_profiles": bounded_profiles,
        "enumerated_tapes_counting_each_profile": tapes,
        "order_sensitive_shifted_batch": {"field": 7, "rho": 3,
            "residual_1_2_result": 0, "residual_2_1_result": 6},
        "complete_strategy_search": False,
        "QM31_security_measurement": False,
        "result": "PASS"
    }, indent=2))


if __name__ == "__main__":
    main()
