#!/usr/bin/env python3
"""Exact IID candidate-tape counts, NOT a source-oracle probability claim."""
from fractions import Fraction
from math import log2


def counts(n, k, cap):
    # (distinct accepted, distinguished pair elements accepted) -> tape count.
    states = {(0, 0): 1}
    for _ in range(cap):
        following = {}
        def add(key, mass):
            following[key] = following.get(key, 0) + mass
        for (j, b), mass in states.items():
            if j == k:
                add((j, b), n * mass)  # ignored suffix: success is absorbing
            else:
                add((j, b), j * mass)
                if b < 2:
                    add((j + 1, b + 1), (2 - b) * mass)
                if n - 2 - (j - b) > 0:
                    add((j + 1, b), (n - 2 - (j - b)) * mass)
        states = following
        assert sum(states.values()) == n ** (_ + 1)
    success = sum(m for (j, _), m in states.items() if j == k)
    bad_success = states.get((k, 2), 0)
    assert Fraction(bad_success, success) == Fraction(k * (k - 1), n * (n - 1))
    return success, bad_success, n ** cap


def main():
    # Independent exhaustive small-domain check of the counting recurrence.
    from itertools import product
    for n, k, cap in [(3, 2, 4), (4, 3, 5)]:
        success = bad = 0
        for tape in product(range(n), repeat=cap):
            accepted = list(dict.fromkeys(tape))[:k]
            success += len(accepted) == k
            bad += len(accepted) == k and 0 in accepted and 1 in accepted
        assert (success, bad, n ** cap) == counts(n, k, cap)
    success, bad, total = counts(2 ** 18, 22, 64)
    failure = Fraction(total - success, total)
    print('model: 64 IID uniform words in Fin(2^18); no release filter')
    print('conditional_pair_probability:', Fraction(bad, success))
    print('failure_probability_exact:', failure)
    print('failure_log2:', log2(failure.numerator) - log2(failure.denominator))
    print('unconditioned_bad_and_success_exact:', Fraction(bad, total))
    print('source_oracle_and_publication_refinement: NOT ESTABLISHED')


if __name__ == '__main__':
    main()
