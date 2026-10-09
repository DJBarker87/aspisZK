#!/usr/bin/env python3
"""Exact arithmetic screen for the regular higher-Y support/query tail.

This is a consumer of the proved per-factor incidence inequality, not a
probability theorem or a source/Fiat--Shamir bridge.  It assumes a total
causal partition has supplied one selected support size per gamma, the
additive factor budget applies to the union, and fresh uniform distinct
queries follow that selection.
"""

from __future__ import annotations

import json
import math


P = 2**31 - 1
FIELD_CARD = P**4
GAMMA_CARD = FIELD_CARD - 1
FIBRES = 262_144
SYMBOLS = 1_048_576
QUERIES = 22
MIN_SUPPORT = 9_558
SUM_BRANCH_BUDGET = 239_599_331
INCIDENCE_NUMERATOR = SYMBOLS * SUM_BRANCH_BUDGET
QUERY_DENOMINATOR = math.comb(FIBRES, QUERIES)


def tail_cap(support: int) -> int:
    """Union cap from M >= 4*support-2 and (M-1024)|G| <= N*B."""

    denominator = 4 * support - 1_026
    assert denominator > 0
    return min(GAMMA_CARD, INCIDENCE_NUMERATOR // denominator)


def weighted_numerator(max_support: int) -> int:
    """Layer-cake bound, including the known minimum-support base mass."""

    assert MIN_SUPPORT <= max_support <= FIBRES
    return tail_cap(MIN_SUPPORT) * math.comb(MIN_SUPPORT, QUERIES) + sum(
        tail_cap(t) * math.comb(t - 1, QUERIES - 1)
        for t in range(MIN_SUPPORT + 1, max_support + 1)
    )


def passes_weighted(weighted: int, bits: int, include_alpha_roots: bool) -> bool:
    # query mass = weighted/(GAMMA_CARD*QUERY_DENOMINATOR).
    # The optional conservative alpha term is 3/FIELD_CARD.
    lhs = weighted * FIELD_CARD
    if include_alpha_roots:
        lhs += 3 * GAMMA_CARD * QUERY_DENOMINATOR
    rhs = GAMMA_CARD * QUERY_DENOMINATOR * FIELD_CARD
    return lhs * (2**bits) <= rhs


def displayed_bits(weighted: int, include_alpha_roots: bool) -> float:
    probability = weighted / (GAMMA_CARD * QUERY_DENOMINATOR)
    if include_alpha_roots:
        probability += 3 / FIELD_CARD
    return -math.log2(probability)


def main() -> None:
    targets = (100, 105, 110)
    last: dict[int, tuple[int, int]] = {}
    first_failure: dict[int, tuple[int, int]] = {}
    weighted = tail_cap(MIN_SUPPORT) * math.comb(MIN_SUPPORT, QUERIES)
    for support in range(MIN_SUPPORT, FIBRES + 1):
        if support > MIN_SUPPORT:
            weighted += tail_cap(support) * math.comb(support - 1, QUERIES - 1)
        for bits in targets:
            if passes_weighted(weighted, bits, True):
                last[bits] = (support, weighted)
            elif bits not in first_failure:
                first_failure[bits] = (support, weighted)

    thresholds = {}
    for bits in targets:
        support, last_weighted = last[bits]
        failed_support, failed_weighted = first_failure[bits]
        assert failed_support == support + 1
        thresholds[str(bits)] = {
            "last_support_passing": support,
            "bits_at_last_support": displayed_bits(last_weighted, True),
            "first_support_failing": failed_support,
            "bits_at_first_failure": displayed_bits(failed_weighted, True),
        }

    all_support_bits = displayed_bits(weighted, True)
    result = {
        "status": "exact_arithmetic_screen_not_probability_theorem",
        "field_cardinality": FIELD_CARD,
        "nonzero_gamma_cardinality": GAMMA_CARD,
        "fibres": FIBRES,
        "queries": QUERIES,
        "minimum_literal_support": MIN_SUPPORT,
        "sum_fixed_branch_budget": SUM_BRANCH_BUDGET,
        "incidence_numerator": INCIDENCE_NUMERATOR,
        "tail_cap_formula": "floor(1048576*239599331/(4*m-1026))",
        "weighted_query_formula": (
            "[H(9558)*choose(9558,22) + "
            "sum_(m=9559..u) H(m)*choose(m-1,21)] / "
            "((|QM31|-1)*choose(262144,22))"
        ),
        "conservative_alpha_term": "3/|QM31|",
        "thresholds": thresholds,
        "unrestricted_max_support_bits": all_support_bits,
        "unrestricted_max_support_passes_100": passes_weighted(weighted, 100, True),
        "not_established": [
            "acceptance_to_regular_higher_factor_partition",
            "support_above_cutoff_implies_checked_payment_extraction",
            "singular_OOD_pair_root_event",
            "authentication_and_source_refinement",
            "Fiat-Shamir_resource_bound",
        ],
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
