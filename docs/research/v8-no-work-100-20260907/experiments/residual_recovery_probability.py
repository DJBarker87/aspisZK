#!/usr/bin/env python3
"""Exact conditional residual-recovery arithmetic; no source/FS theorem.

Only integer binomials and rational arithmetic are evaluated. There is no
finite-field search, challenge enumeration, simulation, or grinding credit.
The 191250-term sum is evaluated using one shared binomial denominator.
"""

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from math import comb
from pathlib import Path


P = 2147483647
K = P**4
N = K - P**2
T, Q, LOWER, UPPER = 262144, 22, 9558, 200807
TAIL_NUMERATOR = 1048576 * 239599331
MIDDLE_DEGREE, SINGULAR_DEGREE = 65061549, 25345827
MIDDLE_GAMMAS, LOW_GAMMAS = 104, 117049
RECORD = Path(__file__).resolve().parent.parent / "residual-recovery-probability.json"


def tail(m):
    assert 4 * m > 1026
    return TAIL_NUMERATOR // (4 * m - 1026)


def layer_numerator(q, lower, upper, budget):
    """C(lower,q)B(lower)+sum C(m-1,q-1)B(m), m=lower+1..upper."""
    assert 1 <= q <= lower <= upper
    result = comb(lower, q) * budget(lower)
    increment = comb(lower, q - 1)
    for m in range(lower + 1, upper + 1):
        result += increment * budget(m)
        # Next increment is C(m,q-1); the division is exact.
        numerator = increment * m
        denominator = m - q + 1
        assert numerator % denominator == 0
        increment = numerator // denominator
    return result


def layer_by_parts(q, lower, upper, budget):
    """Independent telescoping check, with positive differences B(m)-B(m+1)."""
    result = comb(upper, q) * budget(upper)
    choose = comb(lower, q)
    for m in range(lower, upper):
        result += choose * (budget(m) - budget(m + 1))
        numerator = choose * (m + 1)
        denominator = m + 1 - q
        assert numerator % denominator == 0
        choose = numerator // denominator
    return result


def described(value):
    value = Fraction(value)
    with localcontext() as context:
        context.prec = 65
        decimal = Decimal(value.numerator) / Decimal(value.denominator)
        bits = None if value <= 0 else format(-decimal.ln() / Decimal(2).ln(), ".18f")
        return {
            "numerator": str(value.numerator),
            "denominator": str(value.denominator),
            "decimal_approx": format(decimal, ".24E"),
            "negative_log2_approx": bits,
        }


def self_check():
    # Off-by-one regression: a single support m=3, lower=2, q=2 has weight 3.
    h = lambda m: int(m <= 3)
    assert layer_numerator(2, 2, 4, h) == comb(3, 2) == 3
    assert comb(2, 2) + comb(3, 1) == 4  # incorrect next-index increment
    assert comb(2, 2) == 1  # incorrect omission of the upper endpoint
    for q in (1, 2, 3):
        for support in range(3, 8):
            h = lambda m, support=support: int(m <= support)
            assert layer_numerator(q, 3, 7, h) == comb(support, q)
            assert layer_by_parts(q, 3, 7, h) == comb(support, q)
    assert MIDDLE_DEGREE + SINGULAR_DEGREE == 90407376
    assert MIDDLE_GAMMAS == 40 + 28 + 36
    assert MIDDLE_GAMMAS + LOW_GAMMAS == 117153
    assert tail(LOWER) == 6752623450
    assert 4 * LOWER - 1026 == 37206
    assert 4 * UPPER - 1026 == 802202
    assert TAIL_NUMERATOR % (4 * LOWER - 1026) == 21956
    # Product-root pair is a conservative superset, not equality to the union
    # of the two original pair events: mixed roots must remain included.
    first_roots, second_roots = {0, 1}, {2, 3}
    product_roots = first_roots | second_roots
    offdiag = lambda s: {(x, y) for x in s for y in s if x != y}
    original = offdiag(first_roots) | offdiag(second_roots)
    assert original < offdiag(product_roots)
    assert (0, 2) in offdiag(product_roots) - original
    # At the worst permitted own count, 37 coherent gammas are impossible.
    b = 38227
    assert 37 * (803230 - b) > 28 * (1048576 - b)


def calculate(gamma_card, alpha_card, suffix_card):
    self_check()
    if not 6752623450 <= gamma_card <= K:
        raise ValueError("Gamma.card must be between 6752623450 and |K|")
    if not 1 <= alpha_card <= K or not 1 <= suffix_card <= K:
        raise ValueError("A.card and G.card must be positive and at most |K|")
    numerator = layer_numerator(Q, LOWER, UPPER, tail)
    assert numerator == layer_by_parts(Q, LOWER, UPPER, tail)
    denominator = comb(T, Q)
    layer = Fraction(numerator, denominator)
    epsilon = min(Fraction(1), Fraction(3, alpha_card))
    pair_degree = MIDDLE_DEGREE + SINGULAR_DEGREE
    pair = Fraction(pair_degree * (pair_degree - 1), N * (N - 1))
    gamma_middle = Fraction(MIDDLE_GAMMAS, gamma_card)
    gamma_low = Fraction(LOW_GAMMAS, gamma_card)
    query_layer = (1 - epsilon) * layer / gamma_card
    cubic_alpha = Fraction(3, alpha_card)
    suffix_query = Fraction(Q, suffix_card)
    suffix_alpha = Fraction(18, alpha_card)
    integrated = query_layer + cubic_alpha
    total = pair + gamma_middle + gamma_low + integrated + suffix_query + suffix_alpha
    # A sum of the two original pair bounds is tighter, but is NOT the
    # product-pair bound requested and is not silently substituted for it.
    original_pair_sum = Fraction(
        MIDDLE_DEGREE * (MIDDLE_DEGREE - 1)
        + SINGULAR_DEGREE * (SINGULAR_DEGREE - 1), N * (N - 1)
    )
    assert pair >= original_pair_sum
    assert pair - original_pair_sum == Fraction(
        2 * MIDDLE_DEGREE * SINGULAR_DEGREE, N * (N - 1)
    )
    floor_bits = total.denominator.bit_length() - total.numerator.bit_length()
    while total > Fraction(2) ** (-floor_bits):
        floor_bits -= 1
    while total <= Fraction(2) ** (-(floor_bits + 1)):
        floor_bits += 1
    return {
        "schema": "aspis-v8-residual-recovery-probability-draft-v1",
        "status": "exact arithmetic for a conditional ideal residual composition; not a compiled composition or a Rust/ROM security theorem",
        "grinding_credit_bits": 0,
        "parameters": {
            "base_prime": P, "field_cardinality": str(K),
            "admissible_parameter_count": str(N), "gamma_cardinality": str(gamma_card),
            "alpha_cardinality": str(alpha_card), "suffix_cardinality": str(suffix_card),
            "query_domain": T, "query_count": Q, "support_lower": LOWER,
            "support_upper": UPPER, "pair_degree": pair_degree,
            "middle_pair_degree": MIDDLE_DEGREE, "low_pair_degree": SINGULAR_DEGREE,
            "middle_exception_gammas": MIDDLE_GAMMAS, "low_root_gammas": LOW_GAMMAS,
            "gamma_numerator_total": MIDDLE_GAMMAS + LOW_GAMMAS,
        },
        "layer": {
            "formula": "B(9558)*C(9558,22)+sum[m=9559..200807] B(m)*C(m-1,21), divided by C(262144,22)",
            "tail_formula": "B(m)=floor(1048576*239599331/(4*m-1026))",
            "tail_numerator": str(TAIL_NUMERATOR),
            "tail_at_lower": tail(LOWER), "tail_at_upper": tail(UPPER),
            "summands_including_initial": UPPER - LOWER + 1,
            "integer_numerator": str(numerator), "common_denominator": str(denominator),
            "exact": described(layer), "epsilon": described(epsilon),
        },
        "terms": {
            "product_pair": described(pair),
            "middle_gamma_exceptions": described(gamma_middle),
            "low_common_row_roots": described(gamma_low),
            "low_layer_query": described(query_layer),
            "low_cubic_alpha": described(cubic_alpha),
            "integrated_budget_including_cubic_alpha": described(integrated),
            "shared_suffix_query_once": described(suffix_query),
            "shared_suffix_alpha_once": described(suffix_alpha),
        },
        "total": described(total),
        "total_truncated_at_one": described(min(Fraction(1), total)),
        "exact_dyadic_comparisons": {
            "largest_integer_b_with_total_le_2_neg_b": floor_bits,
            "total_le_2_neg_103": total <= Fraction(1, 2**103),
            "total_le_2_neg_104": total <= Fraction(1, 2**104),
            "total_le_2_neg_105": total <= Fraction(1, 2**105),
        },
        "checks": {
            "binomial_pascal_and_summation_by_parts_agree": True,
            "floor_tail_and_endpoints_checked": True,
            "product_pair_contains_mixed_roots": True,
            "overlap_not_assumed_disjoint": True,
            "suffix_charge_count": 1,
            "gamma_denominator_is_original_domain": True,
        },
        "required_interfaces": [
            "Same fixed C1/C2 before both OOD draws; SAME chosen E and singular obstruction combined before both draws",
            "Checked data, circle/non-west conditions and exact accepted parameters at every successful terminal history",
            "Residual payoff is bounded by unrecovered image-valid high-support event plus the actual LowPrefix event, using the SAME suffix",
            "Original nonempty finite Gamma/A/G means; Gamma.card>=6752623450; q=22 uniform ordered distinct queries",
            "History-uniform abort-preserving ordinary-coin law and finite source continuation, not inferred transcript freshness",
        ],
        "excluded_claims": [
            "acceptance-to-image/support or commitment binding supplied automatically",
            "earlyC1=none implies insufficient own support",
            "all lower-degree or no-good acceptance events are covered by this higher-Y residual partition",
            "source sampler/Fiat-Shamir coupling, payment witness extraction, or zero knowledge",
            "conditioning on successful retries, gamma exceptions, or chosen adaptive finals",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gamma-card", type=int, default=K - 1)
    parser.add_argument("--alpha-card", type=int, default=K)
    parser.add_argument("--suffix-card", type=int, default=K)
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    result = calculate(args.gamma_card, args.alpha_card, args.suffix_card)
    if args.check_recorded:
        if result != json.loads(RECORD.read_text()):
            raise SystemExit("FAIL: recorded arithmetic differs")
        print("PASS: exact residual-recovery arithmetic matches the recorded instance; no source/FS claim")
    else:
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
