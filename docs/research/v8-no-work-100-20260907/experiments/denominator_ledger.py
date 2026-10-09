#!/usr/bin/env python3
"""Exact new-class ledgers, not a global security/extraction certificate."""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path
import linear_factor_ledger


def rational(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def bits(value):
    with localcontext() as context:
        context.prec = 80
        return str(-(Decimal(value.numerator) / Decimal(value.denominator)).ln()
                   / Decimal(2).ln())


def record():
    p = 2**31 - 1
    k = p**4
    n = k - p**2
    degree = (2*117077 + 1)*114687
    sparse_count = 111*28
    copy_lambda_count = 100*16*136
    copy_chi_count = 100*(2*136 - 1)
    pair_model = Fraction(degree**2, n*(n-1))
    sparse_model = Fraction(sparse_count, k-1)
    copy_model = Fraction(copy_lambda_count + copy_chi_count, k-1)
    one_point_model = Fraction(degree, n)
    inherited = linear_factor_ledger.record()
    raw = inherited["previous_local_reduction_ceiling"]
    prior = Fraction(int(raw["numerator"]), int(raw["denominator"]))
    assert degree == 26854534485
    assert sparse_count == 3108
    assert (copy_lambda_count, copy_chi_count) == (217600, 27100)
    assert pair_model < Fraction(1, 2**178)
    assert Fraction(1, 2**90) < one_point_model < Fraction(1, 2**89)
    assert sparse_model < Fraction(1, 2**112)
    assert copy_model < Fraction(1, 2**106)
    assert 697*16 + 52 + 24 + 22*621 + 2*296*26 == 40282
    return {
        "parent_revision": "2f6d82fef294410367aa1781fb924af7c38deab9",
        "target": "Pr[complete repaired acceptance AND bounded checked-payment extraction fails]",
        "field_size": str(k),
        "unchanged_local_reduction_ceiling": rational(prior),
        "unchanged_local_reduction_bits_display": bits(prior),
        "new_events": [
            {
                "event": "a retained linear factor is not gamma-constant-denominator with numerator gamma degree at most28",
                "fixing_prefix": "E depends only on fixed C1/C2 parent, before both OOD points and sequential answers",
                "deterministic_implication": "both actual points are roots of the same nonzero E",
                "degree_cap": degree,
                "theorem": "SelectedLinearCover.exists_selected_classification; LinearDenominatorFactors.exists_parent_obstruction",
                "scope": "all retained linear-Y prime factors, no monicity or supplied rational-root premise",
                "pair_count_upper_bound": str(degree**2),
                "pair_count_theorem": "MonicFactorOOD.pair_root_card_le, generic unchanged theorem",
                "uniform_distinct_K_minus_CM31_model": {
                    "domain_cardinality": str(n),
                    "bound": rational(pair_model), "bits_display": bits(pair_model),
                    "status": "exact arithmetic and finite count; actual bounded sampler/source/FS law not instantiated",
                },
                "one_point_only_diagnostic": {
                    "bound": rational(one_point_model), "bits_display": bits(one_point_model),
                    "passes100": False,
                },
                "global_charge": None,
                "overlap": "supersedes old monic-only OOD obstruction; do not add it again",
            },
            {
                "event": "actual gamma hits sparse original-code specializations in any fixed positive-Y factor",
                "fixing_prefix": "parent and sampled Gamma universe fixed before OOD/gamma; sparse property itself is not rare",
                "set_cardinality_cap": sparse_count,
                "theorem": "LinearMessageFamily.sparseChallenges_card; SelectedLinearCover.exists_selected_classification",
                "uniform_nonzero_gamma_model": {"bound": rational(sparse_model), "bits_display": bits(sparse_model)},
                "scope": "a union of <=111 algebraic sparse sets, NOT111 times a query tail",
                "alternative": "same actual reconstructed message equals batch of a member of a pre-OOD family with at most111 actual29-message tuples",
                "global_charge": None,
            },
            {
                "event": "an adaptively selected member of fixed early-C1 family meets literal selected-copy source premises but has false weighted aliases",
                "fixing_prefix": "family from C1 before lambda; each lambda polynomial fixed then, each chi Wronskian fixed after lambda before chi",
                "source_premises": "local/total/inactive helper identities and all applicable slot-pole exclusions",
                "lambda_root_union_cap": copy_lambda_count,
                "chi_root_union_cap_each_lambda": copy_chi_count,
                "finite_pair_cap": "217600*card(Chi)+27100*card(Lambda)",
                "theorem": "EarlyC1CopyCollision.coveredFailures_card",
                "uniform_nonzero_pair_model": {"bound": rational(copy_model), "bits_display": bits(copy_model)},
                "global_charge": None,
                "overlap": "no import of old396430; source acceptance/own-support/law composition still needed",
            },
        ],
        "remaining_mass": {
            "retained_higher_Y_degree": None,
            "represented29_tuple_without_sufficient_component_own_support": None,
            "represented_and_supported_tuple_without_checked_witness": None,
            "auth_source_replay_abort_fuel_missing_mismatched_challenges": None,
            "resource_bounded_Fiat_Shamir_and_actual_sampler": None,
        },
        "partition_status": "same actual selected-model Root classified; not a total actual-verifier failure partition",
        "global_extraction_bound": None, "global_remaining_allowance": None,
        "body_bytes": 40282, "new_proof_bytes": 0, "new_verifier_operations": 0,
        "new_complete_transaction_CU": None, "new_prover_measurements": None,
        "privacy": "separate full-view simulator still required; no new public messages",
        "grinding_security_credit": 0, "quantum_claim": None,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    result = record()
    if args.check_recorded:
        target = Path(__file__).resolve().parent.parent / "denominator-ledger.json"
        assert json.loads(target.read_text()) == result
        print("Exact class ledger matches; no global extraction certificate asserted.")
    else:
        print(json.dumps(result, indent=2))
