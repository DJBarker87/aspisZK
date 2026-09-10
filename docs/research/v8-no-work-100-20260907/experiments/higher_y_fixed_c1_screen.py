#!/usr/bin/env python3
"""Exact arithmetic screen for the fixed-early-C1 higher-Y split.

This consumes, but does not prove, the proposed disjoint classification:

* regular supports through 200,807 fibres use the checked incidence/query
  layer cake;
* supports at least 200,808 fibres in the dense three-helper branch use one
  fixed degree-28 component curve and the parent's 117,077 weight budget;
* the alternative helper branch has fewer than three good gammas.

The alpha and compact-suffix terms are included once.  This remains an ideal
uniform-challenge arithmetic screen until the event adapter and source/FS
coupling are proved.
"""

from fractions import Fraction
import json
import math


P = 2**31 - 1
K = P**4
GAMMA = K - 1
FIBRES = 262_144
SYMBOLS = 1_048_576
Q = 22
MIN_SUPPORT = 9_558
LOW_SUPPORT_MAX = 200_807
REGULAR_BUDGET = 239_599_331
HIGHER_PARENT_WEIGHT = 117_077
SINGULAR_GAMMAS = 117_049
PAIR_ROOT = Fraction(
    3_244_499_600_849,
    2_284_408_317_668_028_910_234_756_318_256_429_327_990_468_779_241_285_843_698_658_142_054_252_544,
)


def tail_cap(support: int) -> int:
    denominator = 4 * support - 1_026
    assert denominator > 0
    return min(GAMMA, SYMBOLS * REGULAR_BUDGET // denominator)


def low_weighted_numerator() -> int:
    return tail_cap(MIN_SUPPORT) * math.comb(MIN_SUPPORT, Q) + sum(
        tail_cap(m) * math.comb(m - 1, Q - 1)
        for m in range(MIN_SUPPORT + 1, LOW_SUPPORT_MAX + 1)
    )


def bits(value: Fraction) -> float:
    return -math.log2(float(value))


def exact(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def main() -> None:
    query_denominator = math.comb(FIBRES, Q)
    weighted = low_weighted_numerator()
    low_query = Fraction(weighted, GAMMA * query_denominator)
    conservative_alpha = Fraction(3, K)
    high_curve = Fraction(HIGHER_PARENT_WEIGHT, GAMMA)
    suffix = Fraction(Q, GAMMA) + Fraction(18, K)
    dense = low_query + conservative_alpha + high_curve + suffix
    sparse = Fraction(2, GAMMA) + suffix
    # This conservatively charges the singular set again even though its
    # high-support intersection is already contained in high_curve.
    all_higher = dense + Fraction(SINGULAR_GAMMAS, GAMMA) + PAIR_ROOT
    result = {
        "status": "exact_arithmetic_screen_not_global_probability_theorem",
        "field_cardinality": K,
        "nonzero_gamma_cardinality": GAMMA,
        "queries": Q,
        "low_support_interval": [MIN_SUPPORT, LOW_SUPPORT_MAX],
        "high_support_begins": LOW_SUPPORT_MAX + 1,
        "regular_incidence_budget": REGULAR_BUDGET,
        "higher_parent_weight": HIGHER_PARENT_WEIGHT,
        "low_weighted_numerator": str(weighted),
        "terms": {
            "low_query_plus_alpha": {
                **exact(low_query + conservative_alpha),
                "bits_approx": bits(low_query + conservative_alpha),
            },
            "dense_high_curve": {
                **exact(high_curve),
                "bits_approx": bits(high_curve),
            },
            "one_compact_suffix": {
                **exact(suffix),
                "bits_approx": bits(suffix),
            },
            "dense_total": {
                **exact(dense),
                "bits_approx": bits(dense),
                "passes_100": dense * 2**100 < 1,
            },
            "all_higher_conservative_total": {
                **exact(all_higher),
                "bits_approx": bits(all_higher),
                "passes_100": all_higher * 2**100 < 1,
                "double_counts_high_support_singular_intersection": True,
            },
            "sparse_branch": {
                **exact(sparse),
                "bits_approx": bits(sparse),
            },
        },
        "conditional_composition": "max(sparse_branch,dense_total)",
        "proof_body_bytes": 40_282,
        "grinding_credit_bits": 0,
        "theorem_status": {
            "high_support_all_factor_count": "kernel checked",
            "regular_tail_sum": "kernel checked",
            "actual_low_support_query_adapter": "kernel checked",
            "common_regular_row": "kernel checked",
            "generic_finite_layer_cake": "kernel checked",
            "selected_layer_cake_instantiation": "unresolved",
            "complete_acceptance_partition": "unresolved",
            "fiat_shamir_coupling": "unresolved",
            "payment_extraction": "partial deterministic bridges only",
            "full_view_zero_knowledge": "unresolved",
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
