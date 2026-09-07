#!/usr/bin/env python3
"""Independent exact checks, not a proof of Aspis adaptive recovery.

Standard library only. No network, external files, repository writes, or Lean.
Prints rational arithmetic, a shifted-batch sharpness instance, and tests of
query-last finite counting/tail identities. These identities require queries
uniform conditional on the ENTIRE prior prefix; they do not transfer to a
Fiat-Shamir execution automatically.
"""
from fractions import Fraction
from itertools import combinations, product
from math import comb, log2
import json

F = Fraction
P = 2**31 - 1
K = P**4
T = 2**18
Q = 22
J = 9557


def rational(x: F) -> dict:
    return {
        "numerator": str(x.numerator),
        "denominator": str(x.denominator),
        "bits_display_only": -log2(x) if x > 0 else None,
    }


def choose(n: int, q: int) -> int:
    return comb(n, q) if n >= q >= 0 else 0


def subsets(n: int, q: int):
    return [sum(1 << i for i in s) for s in combinations(range(n), q)]


def query_weight(n: int, q: int, matches: int) -> F:
    if not 1 <= q <= n or not 0 <= matches <= n:
        raise ValueError("Need 1 <= q <= n and 0 <= matches <= n")
    return F(choose(matches, q), choose(n, q))


def prefix_checks() -> dict:
    # All match sets and all legal q, explicit subset counting; not simulation.
    cases = 0
    for n in range(1, 9):
        for q in range(1, n + 1):
            schedules = subsets(n, q)
            for match_set in range(1 << n):
                m = match_set.bit_count()
                passing = sum(s & match_set == s for s in schedules)
                assert passing == choose(m, q)
                tail = sum(choose(t - 1, q - 1) for t in range(q, m + 1))
                assert tail == choose(m, q)
                cases += 1

    # Two distinct prior prefixes, arbitrary agreement sets, arbitrary prefix-only
    # outside flags, and non-uniform prefix probabilities 1/3 and 2/3.
    # A chosen candidate may depend arbitrarily on these prior prefixes.
    weighted_cases = 0
    n = 4
    for q in range(1, n + 1):
        schedules = subsets(n, q)
        for a, b, outside_mask in product(range(1 << n), range(1 << n), range(4)):
            masks = [a, b]
            weights = [F(1, 3), F(2, 3)]
            outside = [bool(outside_mask & 1), bool(outside_mask & 2)]
            direct = sum(
                weights[i] * F(sum(s & masks[i] == s for s in schedules), len(schedules))
                for i in range(2) if outside[i]
            )
            prefix_formula = sum(
                weights[i] * query_weight(n, q, masks[i].bit_count())
                for i in range(2) if outside[i]
            )
            tail_formula = F(0)
            for t in range(q, n + 1):
                h = sum(weights[i] for i in range(2)
                        if outside[i] and masks[i].bit_count() >= t)
                tail_formula += F(choose(t - 1, q - 1), choose(n, q)) * h
            assert direct == prefix_formula == tail_formula

            # One coarse breakpoint: low/high bins. This is a real upper bound,
            # but need not improve the unweighted event probability.
            threshold = 2
            low = sum(weights[i] for i in range(2)
                      if outside[i] and masks[i].bit_count() <= threshold)
            high = sum(weights[i] for i in range(2)
                       if outside[i] and masks[i].bit_count() > threshold)
            upper = query_weight(n, q, threshold) * low + high
            assert direct <= upper
            weighted_cases += 1

    # Failure of the fresh-query condition: if the candidate is selected AFTER
    # the schedule, choose its matching set to be precisely that schedule.
    n, q = 4, 2
    schedules = subsets(n, q)
    actual = F(sum(s & s == s for s in schedules), len(schedules))
    falsely_conditioned_formula = query_weight(n, q, q)
    assert actual == 1 and falsely_conditioned_formula == F(1, 6)
    return {
        "all_match_set_and_hockey_stick_cases": cases,
        "weighted_two_prefix_outside_event_cases": weighted_cases,
        "post_query_selection_countermodel": {
            "actual_pass_probability": rational(actual),
            "invalid_query_last_formula": rational(falsely_conditioned_formula),
        },
    }


def shifted_batch_sharpness() -> dict:
    # D(X) = product_{j=1}^{22}(X-j), embedded in QM31 via M31.
    # D = prior - X * sum_i residual_i X^i by setting residual_i=-D.coeff(i+1).
    coeffs = [1]
    for root in range(1, Q + 1):
        nxt = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            nxt[i] = (nxt[i] - root * c) % P
            nxt[i + 1] = (nxt[i + 1] + c) % P
        coeffs = nxt
    prior = coeffs[0]
    residual = [(-c) % P for c in coeffs[1:]]
    assert prior != 0 and residual[-1] != 0 and coeffs[-1] == 1
    for rho in range(1, Q + 1):
        batch = prior - rho * sum(r * pow(rho, i, P) for i, r in enumerate(residual))
        assert batch % P == 0
    for rho in [0, 23, 24, 100, P - 1]:
        batch = prior - rho * sum(r * pow(rho, i, P) for i, r in enumerate(residual))
        assert batch % P != 0
    return {
        "degree": Q,
        "distinct_nonzero_roots": list(range(1, Q + 1)),
        "prior_m31": prior,
        "residual_m31": residual,
        "scope": "q roots possible for arbitrary fixed prior/residuals; not a protocol forgery",
    }


def main():
    b = query_weight(T, Q, J)
    cancellation = F(28, K - 1) + (1 - F(28, K - 1)) * F(3, K)
    wrong_support = (1 - b) * cancellation
    pointwise = b + wrong_support
    rho21, rho22 = F(21, K - 1), F(22, K - 1)
    inventory = F(396430, K - 1)
    screen21, screen22 = pointwise + rho21 + inventory, pointwise + rho22 + inventory
    assert wrong_support < F(1, 2**119)
    assert pointwise + rho22 < F(1, 2**105)
    assert screen22 - screen21 == F(1, K - 1)

    # These are all-zero-fibre SUBEVENTS of historical constructions, NOT the
    # full folded matching support (additional alpha cancellations can exist).
    original_r = F(28 * (T - 9557), K - 1)
    paired_r = F(28 * ((T - 9556) // 2), K - 1)
    subevent_factor = query_weight(T, Q, 9558)
    result = {
        "reviewed_commit": "1803896acf5d8c4ebe769b3927010031faf40e0e",
        "status": "exact arithmetic and finite identity checks only; adaptive tail bounds unproved",
        "fixed_target_arithmetic": {
            "all_common": rational(b),
            "wrong_support_pointwise": rational(wrong_support),
            "total_pointwise": rational(pointwise),
            "general_rho_cancellation": rational(rho22),
            "pointwise_plus_general_rho": rational(pointwise + rho22),
            "conditional_recorded_inventory_screen_21": rational(screen21),
            "conditional_recorded_inventory_screen_22": rational(screen22),
            "difference_in_probability": rational(screen22 - screen21),
            "bits_lost_display_only": log2(float(screen22 / screen21)),
        },
        "query_last_tests": prefix_checks(),
        "shifted_batch_sharpness": shifted_batch_sharpness(),
        "historical_all_zero_fibre_subevents_only": {
            "original": rational(original_r * subevent_factor),
            "paired": rational(paired_r * subevent_factor),
            "warning": "not total accepted outside mass and not a bound on all folded cancellations",
        },
        "limits": [
            "No new bound on the distribution of adaptive final256 agreement.",
            "The uncovered event must be prefix-measurable or covered by a proved partition.",
            "Direct queries must be uniform conditional on the complete pre-query prefix.",
            "A fixed-target bound cannot be conditioned on challenges and reused as if fresh.",
            "No Lean replay, source bridge, simulator, SBF build, or production changes.",
        ],
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
