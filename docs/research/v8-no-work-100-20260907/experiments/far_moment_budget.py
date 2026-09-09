#!/usr/bin/env python3
"""Exact arithmetic screen for the relation-compatible far-final moment.

This is not a security proof.  It records the size a future moment theorem
would have to establish after the already proved gamma/rho/later-round terms.
"""

from decimal import Decimal, getcontext
from fractions import Fraction
from math import comb
import json


getcontext().prec = 90


def bits(value: Fraction) -> str:
    numerator = Decimal(value.numerator)
    denominator = Decimal(value.denominator)
    return str(-((numerator / denominator).ln() / Decimal(2).ln()))


def rational(value: Fraction) -> dict[str, str]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "bits": bits(value),
    }


def main() -> None:
    p = 2**31 - 1
    k = p**4
    q = 22
    domain = 262_144

    # FixedC1FarMoment charges at most 28 gamma roots.  The suffix theorem
    # charges the degree-q rho collision and three later degree-six repairs.
    proved_terms = Fraction(28, k - 1) + Fraction(q, k - 1) + Fraction(18, k)

    caps = {}
    for matching in (9_556, 9_557, 15_334, 15_589, 65_536, 131_072, 196_608, 246_809):
        moment = Fraction(comb(matching, q), comb(domain, q))
        caps[str(matching)] = {
            "pointwise_moment": rational(moment),
            "with_proved_terms": rational(moment + proved_terms),
        }

    allowance_100 = Fraction(1, 2**100) - proved_terms
    allowance_105 = Fraction(1, 2**105) - proved_terms
    assert allowance_100 > 0 and allowance_105 > 0

    print(json.dumps({
        "status": "arithmetic_only_theorem_applicability_unresolved",
        "field_order": str(k),
        "domain": domain,
        "queries": q,
        "proved_suffix_and_root_terms": rational(proved_terms),
        "maximum_remaining_moment_for_100_bits": rational(allowance_100),
        "maximum_remaining_moment_for_105_bits": rational(allowance_105),
        "fixed_matching_count_screens": caps,
        "warning": (
            "A fixed matching-count cap is not proved for adaptive far finals; "
            "the required theorem may instead bound the average moment."
        ),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
