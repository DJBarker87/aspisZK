#!/usr/bin/env python3
"""Exact rational census for the NEW joint no-good-quotient event.

Metadata-sized integer arithmetic only, no field enumeration or proof build.
Prints a record; --check-recorded compares retained JSON without writing it.
The theorem's event is NOT accepted payment-witness extraction failure.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from math import comb
from pathlib import Path


def record():
    k, T, q = (2**31 - 1)**4, 262144, 22
    C, family = 9396508281246, 99
    beta = lambda m: Fraction(comb(m, q), comb(T, q))
    # Independent falling-factorial check of both exact query ratios.
    for m in (9557, 117964):
        product = Fraction(1)
        for j in range(q):
            product *= Fraction(m-j, T-j)
        assert product == beta(m)
    outside = beta(9557) + Fraction(C, k)*beta(117964) + Fraction(127, k)
    early = family*(Fraction(3, k-1)+Fraction(6, k))
    suffix = Fraction(q, k-1)+Fraction(18, k)
    total = outside+early+suffix
    assert total == beta(9557)+Fraction(C, k)*beta(117964)+Fraction(319, k-1)+Fraction(739, k)
    assert total < Fraction(1, 2**100)
    assert 697*16+52+24+q*621+2*296*26 == 40282

    def rational(value):
        return {"numerator": str(value.numerator), "denominator": str(value.denominator)}

    with localcontext() as ctx:
        ctx.prec = 90
        decimal = Decimal(total.numerator)/Decimal(total.denominator)
        bits = -(decimal.ln()/Decimal(2).ln())
        fraction_used = decimal*(Decimal(2)**100)
    return {
        "parent_revision": "f19673b4fe72cf74ae687a926eeae9d1e5a6a52e",
        "event": "ideal causal compact relation accepts AND actual post-alpha final has no image-and-four-row-correct representative in the literal9558-fibre quotient family",
        "theorem": "SelectedCoveredRelation.no_good_quotient_bound",
        "source_wrapper": "CausalCoveredRecovery (same26+3 component/OOD/row constructors; no early decoder success premise)",
        "field_size": str(k), "queries": q, "fibres": T, "family_cap": family,
        "terms": [
            {"name": "off_family_pointwise_moment", "value": rational(outside),
             "formula": "b(9557)+(9396508281246/k)*b(117964)+127/k",
             "prefix": "R fixed before alpha; actual final alpha-adaptive and fixed before fresh queries",
             "hypotheses": "literal selected encoder and both already-proved off-family tails"},
            {"name": "represented_bad_first_collision", "value": rational(early),
             "formula": "99*(3/(k-1)+6/k)",
             "prefix": "family fixed from R before kappa/tau; response0 depends on kappa/tau before alpha",
             "hypotheses": "bad-image2-root versus complementary image-valid wrong-row3-root partition; compact first-boundary identity"},
            {"name": "single_actual_suffix", "value": rational(suffix),
             "formula": "22/(k-1)+18/k",
             "prefix": "queries before rho; each of three later responses before its own challenge",
             "hypotheses": "degree-q shifted batch and actual compact terminal relation"}
        ],
        "joint_bound": rational(total),
        "joint_bound_bits_display": str(bits),
        "fraction_of_2pow_minus100_display": str(fraction_used),
        "strictly_below_2pow_minus100_exactly_checked": True,
        "status": "exact arithmetic; formal status is separately determined by current-source Lean evidence",
        "fresh_law": "ideal conditional uniform full-field alpha/three later alphas, nonzero kappa/tau/rho, uniform distinct queries after complete prefix; gamma averaging uses a uniform per-gamma bound",
        "overlaps": "99 multiplies only image/row and first-repair collisions; rho and three later repairs charged once across represented/off-family classes; do not add previous complete image/near/off-family suffix bounds",
        "remaining_accepted_good_quotient_mass": None,
        "global_accepted_payment_extraction_upper_bound": None,
        "global_remaining_numerical_allowance": None,
        "remaining_obligations": [
            "image-and-row-correct quotient to original component-family coverage with degree2 helpers and degree28 claim errors",
            "selected semantic/copy/ownership/payment enforcement and deterministic/source endpoint",
            "bounded authenticated list access, replay and extraction",
            "actual source and resource-bounded Fiat-Shamir coupling"
        ],
        "full_view_ZK": "separate unresolved requirement",
        "proof_body_bytes": 40282, "new_verifier_operations": 0,
        "new_proof_bytes": 0, "grinding_security_credit": 0,
        "new_complete_transaction_CU": None,
        "quantum_claim": None
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    result = record()
    if args.check_recorded:
        path = Path(__file__).resolve().parent.parent/"covered-relation-ledger.json"
        assert json.loads(path.read_text()) == result
        print("Joint no-good-quotient rational ledger matches; global extraction mass remains symbolic.")
    else:
        print(json.dumps(result, indent=2))
