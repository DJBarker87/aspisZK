#!/usr/bin/env python3
"""Exact represented/insufficient-own-support class ledger, not global security."""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb
import json
from pathlib import Path


def rational(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def bits(value):
    with localcontext() as context:
        context.prec = 80
        return str(-(Decimal(value.numerator)/Decimal(value.denominator)).ln()/Decimal(2).ln())


def record():
    p, q, t = 2**31-1, 22, 262144
    k = p**4
    size, degree, common_cap, symbols = 111, 28, 9556, 1048576
    exception_cap = degree*symbols
    beta = Fraction(comb(common_cap, q), comb(t, q))
    common = beta*Fraction(exception_cap, k-1)
    outside = Fraction(degree, k-1)+(1-Fraction(degree, k-1))*Fraction(3, k)
    bound = size*(common+outside)
    # Independent integer counting normalization of the same coarse theorem.
    numerator = size*(comb(common_cap, q)*(exception_cap*k)
                     +comb(t, q)*(degree*k+(k-1-degree)*3))
    assert bound == Fraction(numerator, comb(t, q)*(k-1)*k)
    assert exception_cap == 29360128
    assert Fraction(1, 2**113) < bound < Fraction(1, 2**112)
    assert 697*16+52+24+22*621+2*296*26 == 40282
    return {
        "parent_revision": "ed41b2537e7dad15ce8055d9e5524e337ee8b9a4",
        "target": "Pr[complete repaired acceptance AND bounded checked-payment extraction fails]",
        "field_size": str(k),
        "new_restricted_event": {
            "event": "pointwise query success on a literal covered image-valid quotient represented by a fixed-family tuple whose componentwise own support has fewer than38228 symbols; actual final is its true fold; queried poles reject",
            "fixing_prefix": "C1 before lambda/chi; C2 adaptive then fixed; family fixed after C2 before gamma; checked chord/OOD data before gamma; gamma then alpha; fresh q-subset queries",
            "adaptivity": "represented Q and true final may depend on gamma and alpha; existential capture is even larger than causal choice",
            "ideal_law": "conditional independent uniform nonzero gamma, full-field alpha and uniform distinct22-subset of the ORIGINAL262144 fibres",
            "family_cardinality_cap": size,
            "gamma_degree": degree,
            "own_support_symbols_threshold": 38228,
            "common_fibres_cap": common_cap,
            "exception_gamma_cap": exception_cap,
            "exact_fine_count_upper_bound": "sum_p [choose(J_p,q)*e_p*card(A)+(choose(T,q)-choose(J_p,q))*(28*card(A)+(card(G)-28)*3)]",
            "coarse_probability": rational(bound),
            "bits_display_not_certificate": bits(bound),
            "one_member_common_term": rational(common),
            "one_member_outside_term": rational(outside),
            "common_schedule_probability": rational(beta),
            "theorems": ["OwnSymbolCollision.excess_matching_mem_exception", "SelectedOwnSymbol.covered_forces_exception", "TupleQueryTransport.query_zero_iff", "InsufficientOwnSupportFamily.family_joint_count", "SelectedOwnSupportGame.literal_family_count"],
            "applicability": "selected mathematical quotient/query interface; conditional product-law normalization; not yet actual verifier/source/FS composition",
            "global_charge": None,
            "overlap": "alternative to charging an unweighted family query tail on this represented class; no row/image/rho/later repair terms added here",
        },
        "remaining_mass": {
            "outside_literal_family_or_unrepresented_final": "retained prior off-family/false-final obligations; not removed by the restricted event",
            "retained_higher_Y_degree_or_unclassified_candidates": None,
            "covered_represented_true_final_with_insufficient_own_support": "new restricted bound above, global composition still required",
            "own_supported_tuple_without_payment_constraints_or_checked_witness": None,
            "scalar_acceptance_without_pointwise_success_and_off_final_cases": "reuse prior causal relation/query bad events ONCE; not recomposed here",
            "source_auth_replay_fuel_abort_missing_mismatched_challenges": None,
            "bounded_extractor_and_Fiat_Shamir_sampler_resources": None,
        },
        "global_extraction_bound": None,
        "global_remaining_allowance": None,
        "proof_body_bytes": 40282,
        "new_proof_bytes": 0,
        "new_verifier_operations": 0,
        "new_complete_transaction_CU": None,
        "new_prover_measurements": None,
        "privacy": "separate full-view simulation requirement; no new messages",
        "grinding_security_credit": 0,
        "quantum_claim": None,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    result = record()
    if args.check_recorded:
        assert json.loads((Path(__file__).resolve().parent.parent/"own-support-ledger.json").read_text()) == result
        print("Exact restricted-class ledger matches; global bound remains symbolic.")
    else:
        print(json.dumps(result, indent=2))
