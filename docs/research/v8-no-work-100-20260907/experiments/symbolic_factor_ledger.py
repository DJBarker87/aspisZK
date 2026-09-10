#!/usr/bin/env python3
"""Exact metadata for the stronger same-execution identity-factor reduction.

Reuses the existing ceiling; no parameter sweep, field search, or assumption
that a retained factor root is a checked payment witness.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path
import component_ood_ledger


def record():
    previous = component_ood_ledger.record()
    k = int(previous["parameters"]["field_size"])
    old = previous["terms"][0]["value"]
    old = Fraction(int(old["numerator"]), int(old["denominator"]))
    term = Fraction(117077, k-1)
    local = old+term
    old_local = previous["local_reduction_ceiling"]
    assert local == Fraction(int(old_local["numerator"]), int(old_local["denominator"]))
    assert local < Fraction(1, 2**100)
    assert 697*16+52+24+22*621+2*296*26 == 40282

    def rational(value):
        return {"numerator": str(value.numerator), "denominator": str(value.denominator)}

    def bits(value):
        with localcontext() as ctx:
            ctx.prec = 90
            return str(-(Decimal(value.numerator)/Decimal(value.denominator)).ln()/Decimal(2).ln())

    return {
        "parent_revision": "f0f46ffede8812252ac7cee9edf5547f228533d5",
        "theorem": "AspisV8.CausalFactorReduction.total_reduction",
        "experiment": "same selected source-shaped compact-suffix causal ideal game, conditional on the literal checked chord/circle/chart prefix",
        "target_not_yet_proved": "Pr[complete repaired verifier accepts AND specified bounded extractor fails to return a checked payment witness]",
        "parameters": previous["parameters"],
        "terms": [
            {"name": "missing_good_quotient", "value": rational(old),
             "event": "accepted compact suffix with no covered image-valid row-correct quotient folding to the actual final",
             "theorem": "CausalCoveredRecovery.missing_bound",
             "overlap": "already includes shifted rho and all four relation repairs; not added again"},
            {"name": "good_quotient_outside_identity_factor_family", "value": rational(term),
             "event": "accepted good-quotient suffix without any same-Q reconstruction rooted in a positive-Y global factor having BOTH actual OOD polynomial identities",
             "theorem": "CausalFactorReduction.outside_bound",
             "fixing_prefix": "P fixed from C1/C2 before OOD; both sequential OOD answers/points fix one exception polynomial and retained factor family before gamma",
             "fresh_challenge": "uniform nonzero QM31 gamma conditional on the entire ideal prefix",
             "exact_degree_bound": 117077,
             "construction": "product of nonzero chosen OOD-substitution polynomials for excluded positive-Y factors and nonzero coefficient polynomials for Y-constant factors; retained factors contribute1",
             "degree_justification": "sum of all prime-factor Y/Z weights is at most parent weight; parent h+28*j<117078",
             "adaptivity": "universal over all gamma-dependent reconstructed polynomials and all later alpha-dependent final choices satisfying the actual same-Q bridge",
             "repeated_factors": "included with multiplicity; no squarefree or nonzero-parent-derivative premise",
             "replaces_previous_OOD_nonidentity_charge": True,
             "extra_derivative_content_zero_specialization_factor_union_charges": False}
        ],
        "local_reduction_ceiling": rational(local),
        "local_reduction_bits_display": bits(local),
        "factor_exception_bits_display": bits(term),
        "arithmetic_ceiling_unchanged": True,
        "local_difference_not_global_allowance": rational(Fraction(1, 2**100)-local),
        "retained_factor_branch": {
            "definition": "CausalFactorReduction.factorProbability: actual accepted suffix with the same Q covered, image-valid, ordinary-row-correct, folding to its actual final, and its actual reconstructed polynomial rooted in a pre-gamma both-identity factor",
            "remaining_mass": None,
            "factor_cardinality_upper_bound": 111,
            "cardinality_evidence": "derived from existing positiveYPrimeFactors_card_le_natDegree and curveTrivariatePolynomial_natDegree_lt at yRows112; not a newly audited specialized cardinal declaration",
            "not": "not111 component tuples, not original-code component membership, not an efficient decoder or checked payment witness",
            "honest_singular_parent_allowed": True},
        "secondary_regular_branch": {
            "theorem": "SelectedFactorCoherence.selected_fixed_factor",
            "conditional_degree_bound": 117049,
            "included_in_primary_ledger": False,
            "reason": "the stronger family cover handles singular/repeated parents directly; derivative terms must not be added again"},
        "global_extraction_bound": None,
        "global_remaining_allowance": None,
        "unclosed_layers": [
            "retained identity-factor roots to original component recovery, including exceptional rational-helper specializations",
            "fixed early C1 to semantic/copy constraints and checked payment extraction",
            "authenticated opening/replay access, retries, fuel/abort, cached/advance mismatches and specified extractor runtime",
            "complete corrected Rust/source and actual transcript/sampler correspondence",
            "resource-bounded Fiat-Shamir lift and full-view privacy simulation"],
        "privacy": "separate unresolved full adaptive-view simulation; this turn adds no protocol messages",
        "body_bytes": 40282, "new_proof_bytes": 0, "new_verifier_operations": 0,
        "new_complete_transaction_CU": None, "new_prover_measurements": None,
        "grinding_security_credit": 0, "quantum_claim": None,
        "status": "exact rational reduction ledger; formal completion limited to the named source-shaped ideal-game endpoints"
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    value = record()
    if args.check_recorded:
        target = Path(__file__).resolve().parent.parent/"symbolic-factor-ledger.json"
        assert json.loads(target.read_text()) == value
        print("Exact factor-cover ledger matches; global extraction remains unbounded.")
    else:
        print(json.dumps(value, indent=2))
