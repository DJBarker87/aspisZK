#!/usr/bin/env python3
"""Exact off-family tail composition, not a global V8 certificate.

The selected finite-parameter result depends on the masked curve-tail and
four-support/averaging theorem interfaces being instantiated. Arithmetic does
not discharge those interfaces. No field enumeration or probabilistic test.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
import json
from math import comb


def record(x):
    with localcontext() as context:
        context.prec = 75
        bits = -(Decimal(x.numerator)/Decimal(x.denominator)).ln()/Decimal(2).ln()
    return {"numerator": str(x.numerator), "denominator": str(x.denominator),
            "bits_display": str(bits)}


def finite_incidence_checks():
    """All support multisets in small games, up to node-label symmetry."""
    count = 0
    for size in range(2, 5):
        for nodes in range(4, 7):
            fours = tuple(combinations(range(nodes), 4))
            for masks in combinations_with_replacement(range(1 << size), nodes):
                loads = [sum((mask >> point) & 1 for mask in masks)
                         for point in range(size)]
                incidences = sum(comb(load, 4) for load in loads)
                independent = 0
                largest_intersection = 0
                for subset in fours:
                    intersection = (1 << size) - 1
                    for node in subset:
                        intersection &= masks[node]
                    common = intersection.bit_count()
                    independent += common
                    largest_intersection = max(largest_intersection, common)
                assert independent == incidences
                h = sum(loads)//size
                assert size*comb(h, 4) <= incidences
                average = Fraction(size*comb(h, 4), comb(nodes, 4))
                assert average <= largest_intersection
                count += 1
    return count


def result():
    T, a, t, n, q = 262144, 9558, 117965, 128, 22
    k = (2**31 - 1)**4
    old_cap = 9396508281246
    h = n*t//T
    assert h == 57 and h*T <= n*t
    certificate = Fraction(T*comb(h,4), comb(n,4))
    assert certificate == Fraction(30818304,3175) and certificate >= a
    assert 255 < a <= t <= T
    # Independent falling-product computation verifies both finite query ratios.
    def query(m):
        falling = Fraction(1)
        for j in range(q):
            falling *= Fraction(m-j,T-j)
        exact = Fraction(comb(m,q),comb(T,q))
        assert exact == falling
        return exact
    low = query(a-1)
    middle = Fraction(old_cap,k)*query(t-1)
    high = Fraction(n-1,k)
    pointwise = low+middle+high
    scalar = Fraction(q,k-1)+Fraction(18,k)
    suffix = pointwise+scalar
    assert pointwise < Fraction(1,2**104)
    assert suffix < Fraction(1,2**104)
    # This is a candidate-family cardinality screen. Applicability must use
    # the JOINT tuple overlap, not silently import an RS code for raw slots.
    johnson = Fraction(T*(a-255), a*a-T*255)
    return {
        "parent_revision": "b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9",
        "parameters": {"field_cardinality": str(k), "domain": T, "queries": q,
                       "family_own_support_floor": a, "middle_upper_matching": t-1,
                       "high_threshold": t, "high_forbidden_alpha_count": n,
                       "existing_degree_three_cap": old_cap},
        "support_certificate": {"minimum_load_floor": h,
                                "sum_incidence_lower": str(T*comb(h,4)),
                                "four_subsets": str(comb(n,4)),
                                "average_intersection_numerator": str(certificate.numerator),
                                "average_intersection_denominator": str(certificate.denominator),
                                "forces_intersection_at_least": a},
        "terms": [
            {"event": "off-family actual adaptive final has M<a and all queries match",
             "bound": record(low), "prefix": "actual final before fresh queries",
             "family_query_multiplier": 1},
            {"event": "off-family actual adaptive final has a<=M<t and all queries match",
             "bound": record(middle), "prefix": "fixed received lanes before alpha; actual final before queries",
             "cardinality_input": "masked existing degree-three curve theorem; not unconditional whole-family success"},
            {"event": "off-family actual adaptive final has M>=t and all queries match",
             "bound": record(high), "prefix": "fixed received lanes before alpha",
             "cardinality_input": "128 such alphas force four-support intersection and actual candidate coverage"}],
        "off_family_pointwise_ceiling": record(pointwise),
        "shifted_query_and_three_later_repairs": record(scalar),
        "off_family_scalar_suffix_ceiling": record(suffix),
        "overlap": "These are one supported off-family class. Do not add other ceilings counting the same rho/tail repairs.",
        "not_included": ["covered image/ordinary/gamma/component branches", "authentication/source mismatch", "bounded replay/extractor failures", "payment knowledge", "resource-bounded FS", "full-view ZK"],
        "global_accepted_extraction_bound": None,
        "remaining_global_allowance": None,
        "joint_family_johnson_screen": record(johnson),
        "small_support_multiset_cases": finite_incidence_checks(),
        "small_test_scope": "exhaustive support multisets up to node-label permutation for T2..4 and n4..6; not a cryptographic experiment",
        "proof_body_bytes": 697*16+52+24+22*621+2*296*26,
        "positive_work_credit": 0,
        "status": "exact arithmetic; theorem and selected-source instantiation status recorded separately"
    }


if __name__ == "__main__":
    print(json.dumps(result(), indent=2))
