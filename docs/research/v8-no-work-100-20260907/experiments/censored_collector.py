#!/usr/bin/env python3
"""Exact tiny causal collector controls; no cryptographic field enumeration.

The policy observes each fresh uniform query set before retaining or discarding
it. Dynamic programming ranges over ALL such causal policies in this reduced
game, including acceptance censorship. It does not provide prover successes,
authenticated openings, or common support across different final polynomials.
"""
import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import json
from math import comb, log2
from pathlib import Path


def rational(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def optimum(t, q, cap, draws, matching=None):
    """Adaptive retention; a retained query must match one fixed final."""
    threshold = cap - q + 2
    schedules = tuple(sum(1 << i for i in s) for s in combinations(range(t), q))
    matching = (1 << t) - 1 if matching is None else matching

    @lru_cache(None)
    def value(left, union, successes):
        if union.bit_count() > cap:
            return Fraction(0)
        if successes >= threshold:
            return Fraction(1)
        if successes + left < threshold:
            return Fraction(0)
        discard = value(left - 1, union, successes)
        total = Fraction(0)
        for schedule in schedules:
            retain = Fraction(0)
            if schedule & ~matching == 0:
                retain = value(left - 1, union | schedule, successes + 1)
            total += max(discard, retain)
        return total / len(schedules)

    return value(draws, 0, 0), value.cache_info().currsize


def result():
    rows = []
    for t in range(3, 9):
        for q in range(1, min(2, t - 1) + 1):
            for cap in range(q, min(4, t - 1) + 1):
                threshold = cap - q + 2
                for extra in range(3):
                    draws = threshold + extra
                    exact, states = optimum(t, q, cap, draws)
                    bound = draws * Fraction(comb(cap, q), comb(t, q))
                    assert exact <= min(Fraction(1), bound)
                    rows.append({"domain": t, "queries": q, "cap": cap,
                                 "draws": draws, "success_threshold": threshold,
                                 "optimum": rational(exact), "bound": rational(bound),
                                 "states": states})

    # An accepted-only query distribution need not remain uniform: retain
    # exactly those schedules contained in the fixed three-point match set.
    conditional = Fraction(comb(3, 2), comb(8, 2))
    assert conditional == Fraction(3, 28) and conditional != 1
    # Threshold is sharp deterministically: q points first, then one new
    # point per retained schedule achieves cap with cap-q+1 successes.
    t, q, cap = 8, 2, 4
    growth = [{0, 1}, {0, 2}, {0, 3}]
    union = set()
    for schedule in growth:
        assert len(schedule) == q and not schedule <= union
        union |= schedule
    assert len(growth) == cap - q + 1 and len(union) == cap

    # Different finals can have disjoint large matching supports. Successful
    # collection of each support alone gives no common-support certificate.
    sets = [set(range(4)), set(range(4, 8))]
    assert all(len(s) > 1 for s in sets) and not sets[0] & sets[1]
    k = (2**31 - 1)**4
    stagnation = Fraction(comb(255, 22), comb(262144, 22))
    assert stagnation < Fraction(1, 2**221)
    body = 697*16 + 52 + 24 + 22*621 + 2*296*26
    assert body == 40282
    return {
        "scope": "exact backward induction over all causal retain/discard policies in tiny fixed-final query games",
        "not_executed": ["QM31 enumeration", "actual Merkle replay", "payment extraction", "SBF/CU"],
        "small_games": rows,
        "censoring_regression": {"unconditional_subset_probability": rational(conditional),
                                 "subset_probability_given_retention": rational(Fraction(1))},
        "selected_profile": {"field_cardinality": str(k), "domain": 262144,
                             "queries": 22, "support_cap": 255,
                             "qualifying_success_threshold": 235,
                             "one_draw_stagnation_bound": rational(stagnation),
                             "display_bits": log2(stagnation.denominator)-log2(stagnation.numerator),
                             "bounded_draw_event_bound": "min(1, N * one_draw_stagnation_bound)",
                             "event": "at least235 retained continuations at one frozen final/query boundary, final support union at most255",
                             "hypotheses": ["fresh uniform distinct q-subset conditional on full history", "retained query values root-bound to same fixed oracle", "explicit pointwise checks", "all draws including aborts counted in N"],
                             "global_knowledge_bound": None, "useful_fork_collection_bound": None,
                             "proof_body_bytes": body},
        "formal_status": "symbolic derivation in collector review; not a Lean probability theorem",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-recorded", type=Path)
    args = parser.parse_args()
    payload = json.dumps(result(), indent=2) + "\n"
    if args.check_recorded:
        assert args.check_recorded.read_text() == payload
        print("censored collector exact controls and recorded rationals agree")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
