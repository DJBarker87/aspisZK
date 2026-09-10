#!/usr/bin/env python3
"""Exact local/class ledgers; deliberately no global extraction certificate."""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path
import symbolic_factor_ledger


def rational(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def display_bits(x):
    with localcontext() as ctx:
        ctx.prec = 80
        return str(-(Decimal(x.numerator)/Decimal(x.denominator)).ln()/Decimal(2).ln())


def record():
    previous = symbolic_factor_ledger.record()
    p = 2**31-1
    k = p**4
    n = k-p**2
    pair = Fraction(114687**2, n*(n-1))
    sparse = Fraction(28, k-1)
    old = previous["local_reduction_ceiling"]
    old = Fraction(int(old["numerator"]), int(old["denominator"]))
    assert k == int(previous["parameters"]["field_size"])
    assert 697*16+52+24+22*621+2*296*26 == 40282
    assert pair < Fraction(1, 2**214)
    assert sparse < Fraction(1, 2**119)
    return {
        "parent_revision": "6f1ebbe55fcc6fd008071329d5270aae0521cf9a",
        "target": "Pr[complete repaired acceptance AND specified bounded checked-payment extraction fails]",
        "previous_local_reduction_ceiling": rational(old),
        "previous_local_reduction_bits_display": display_bits(old),
        "local_reduction_unchanged": True,
        "new_class_information": [
            {
                "event": "a retained monic linear factor has root-curve gamma degree above28",
                "fixing_prefix": "one nonzero E(X) constructed from C1/C2 parent before either OOD point",
                "implication": "E(t0)=E(t1)=0, deg(E)<=114687; same actual reconstructed Q",
                "theorems": ["MonicFactorOOD.exists_parent_ood_obstruction", "MonicFactorOOD.pair_root_card_le", "SelectedMonicCover.exists_selected_classification"],
                "finite_pair_numerator_upper_bound": 114687**2,
                "conditional_uniform_distinct_K_minus_CM31_model": {
                    "domain_cardinality": str(n),
                    "bound": rational(pair), "bits_display": display_bits(pair),
                    "status": "arithmetic model plus proved finite count; literal bounded sampler/source/FS law NOT instantiated",
                },
                "global_charge": None,
                "factor_count_multiplier": False,
            },
            {
                "event": "in the sparse-good branch for a fixed prime linear factor, the actual fresh nonzero gamma belongs to its good original-code specialization set",
                "fixing_prefix": "factor, root and code image before actual gamma",
                "bound_under_fresh_uniform_nonzero_gamma": rational(sparse),
                "bits_display": display_bits(sparse),
                "theorem": "LinearFactorInterpolation.rational_29_dichotomy with concrete-code/prime bridges",
                "alternative": "one actual29-component message curve covers all polynomial roots",
                "sparse_branch_property_is_not_itself_a_rare_event": True,
                "global_charge": None,
                "reason_not_composed": "per-factor class result; full family partition, own-support, early-C1 and extraction coupling still required",
            },
            {
                "event": "a polynomial root of a positive-Y prime linear factor has zero specialized A coefficient",
                "status": "formally impossible, derived from primitivity and actual root",
                "theorem": "PrimeFactorRegularity.prime_linear_root_regular",
                "extra_exception_term": False,
            },
            {
                "event": "the rational-helper pole control admits any polynomial root at nonzero gamma",
                "classification": "exactly gamma=b and U=0",
                "nonzero_good_cardinality_upper_bound": 1,
                "theorem": "RationalHelperSpecialization.polynomial_root_iff",
                "global_charge": None,
                "scope": "this symbolic obstruction, not all received words or a payment acceptance event",
            },
        ],
        "selected_copy_partition": {
            "theorem": "SelectedCopyAliasQM31.qm31_source_roots_or_aliases",
            "conditions": "literal local residuals, total/inactive helper identities, all applicable slot poles excluded",
            "lambda_error_degree_at_most": "16 * actual_active_link_count",
            "chi_error_degree_strictly_below": "2 * actual_active_link_count",
            "actual_active_link_count_at_most": 136,
            "lambda_fixing": "table and active public layout before lambda; this causality is not supplied by a post-C2 tuple",
            "chi_fixing": "table/layout and lambda before chi",
            "success_alternative": "all actual weighted tuple aliases, including the seven transfer amount-cell edges",
            "global_probability_charge": None,
            "source_acceptance_to_premises": "still required",
        },
        "remaining_mass": {
            "other_retained_factor_classes": None,
            "component_own_support_and_early_C1_projection": None,
            "tuple_to_checked_witness": None,
            "auth_source_replay_fuel_abort_missing_mismatch": None,
            "resource_bounded_Fiat_Shamir": None,
        },
        "global_extraction_bound": None,
        "global_remaining_allowance": None,
        "overlap_policy": "do not add new class models blindly to old ceiling; no repeated relation repairs, content, derivative or historical396430 charge",
        "body_bytes": 40282,
        "new_proof_bytes": 0, "new_verifier_operations": 0,
        "new_complete_transaction_CU": None, "new_prover_measurements": None,
        "privacy": "separate unresolved full-view simulator; no new public messages",
        "grinding_security_credit": 0, "quantum_claim": None,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    result = record()
    if args.check_recorded:
        target = Path(__file__).resolve().parent.parent/"linear-factor-ledger.json"
        assert json.loads(target.read_text()) == result
        print("Exact local/class ledger matches; global extraction remains unbounded.")
    else:
        print(json.dumps(result, indent=2))
