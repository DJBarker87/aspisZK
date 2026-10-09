#!/usr/bin/env python3
"""Exact arithmetic for the new same-execution OOD-identity reduction.

This does not bound identity-branch extraction failures, FS or privacy.
Only small integer/rational metadata arithmetic; no concrete-field search.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path
import covered_relation_ledger


def record():
    previous = covered_relation_ledger.record()
    k = int(previous["field_size"])
    old = Fraction(int(previous["joint_bound"]["numerator"]),
                   int(previous["joint_bound"]["denominator"]))
    # Direct weighted monomial extremum, independent of the displayed cap.
    degree = max(h + 28*j for j in range(112)
                 for h in (117078 - 28*j - 1,))
    assert degree == 117077
    assert 9558*4 - 2 == 38230 > 38229
    new = Fraction(degree, k-1)
    local = old + new
    target = Fraction(1, 2**100)
    assert local < target
    assert 697*16 + 52 + 24 + 22*621 + 2*296*26 == 40282

    def rational(x):
        return {"numerator": str(x.numerator), "denominator": str(x.denominator)}

    def bits(x):
        with localcontext() as ctx:
            ctx.prec = 90
            d = Decimal(x.numerator)/Decimal(x.denominator)
            return str(-d.ln()/Decimal(2).ln())

    return {
        "parent_revision": "9254b2416c3f8c3c488d0475a00d812fee836e00",
        "event": "actual selected causal compact-suffix acceptance outside the retained prefix-fixed pair of symbolic OOD identities",
        "source_theorems": ["CoveredOriginalSymbols.selected_width29_valid",
            "CoveredOODGRS.original_grs_at_ood", "SelectedOODGate.covered_gate_zero",
            "CausalOODReduction.total_reduction"],
        "parameters": {"field_size": str(k), "queries": 22, "fibres": 262144,
            "body_bytes": 40282, "interpolant_x_bound": 114688,
            "interpolant_y_rows": 112, "interpolant_gamma_bound": 117078,
            "component_answer_degree": 28, "helper_curve_degree_unchanged": 2},
        "support": {"quotient_complete_fibres": 9558, "quotient_symbols": 38232,
            "maximum_lost_pole_symbols": 2, "original_symbols": 38230,
            "original_V7_strict_threshold": 38229},
        "terms": [
            {"name": "previous_missing_good_quotient_ceiling", "value": rational(old),
             "theorem": "CausalCoveredRecovery.missing_bound",
             "overlap": "already includes the four relation repairs and degree-q rho; do not add them again"},
            {"name": "good_quotient_nonidentity_OOD_gamma", "value": rational(new),
             "theorem": "CausalOODReduction.nonidentity_good_bound",
             "fixing_prefix": "C1/C2 first determine one nonzero trivariate interpolant; both actual sequential OOD points/answer rows then fixed before gamma",
             "fresh_challenge": "gamma uniform in nonzero QM31 conditional on that entire ideal prefix",
             "event": "image-valid covered quotient exists but at least one fixed normalized OOD substitution is a nonzero polynomial",
             "numerator_reason": "h+28*j<117078; all compatible adaptive candidates force the same polynomial to vanish at gamma",
             "no_family_union": True,
             "hypotheses": "actual circle/checked chord/west exclusions and derived quotient-to-original/GRS identities; symbolic pair-of-zero-identities case kept separately"}
        ],
        "new_component_bits_display": bits(new),
        "local_reduction_ceiling": rational(local),
        "local_reduction_bits_display": bits(local),
        "local_ceiling_below_2pow_minus100_exactly_checked": True,
        "unused_local_difference_not_a_global_allowance": rational(target-local),
        "retained_identity_branch": {
            "definition": "for both actual OOD rows r, P(t_r,A_r(Gamma),Gamma) is identically zero as a polynomial; A_r multiplies all29 actual answers by (1+t_r^2)^512",
            "remaining_mass": None,
            "not": "not component-family membership, decoder success or a checked payment witness"},
        "global_accepted_extraction_failure_bound": None,
        "global_remaining_numerical_allowance": None,
        "remaining_layers": ["symbolic OOD identity branch to original components with fixed early C1",
            "selected semantic/copy and literal payment-witness enforcement",
            "bounded authenticated candidate access/enumeration and replay failures",
            "actual source refinement and resource-bounded Fiat-Shamir lift"],
        "ideal_vs_FS": "the displayed bound is causal ideal uniform sampling only; retries/prequeries/forks and actual sampler resources remain separate",
        "interpolant_access": "noncomputable analysis object from existing V7 existence theorem; not a practical candidate-list algorithm",
        "full_view_ZK": "separate unresolved full-view simulation",
        "new_proof_bytes": 0, "new_verifier_operations": 0,
        "new_complete_transaction_CU": None, "new_prover_time": None,
        "grinding_security_credit": 0, "quantum_claim": None,
        "status": "exact arithmetic; formal status is determined by frozen current-source Lean evidence"
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    result = record()
    if args.check_recorded:
        target = Path(__file__).resolve().parent.parent/"component-ood-ledger.json"
        assert json.loads(target.read_text()) == result
        print("Exact OOD reduction ledger matches; identity-branch extraction remains symbolic.")
    else:
        print(json.dumps(result, indent=2))
