#!/usr/bin/env python3
"""Exact adaptive-tail obstruction accounting, not a full security theorem.

No fitted probabilities, full domain enumeration, network access or file writes.
The old gamma budget is only a diagnostic, not assumed applicable to V8.
"""
from fractions import Fraction as F
from math import comb, log2
from pathlib import Path
import hashlib
import json

P = 2**31-1
K = P**4
T = 2**18
Q = 22
HERE = Path(__file__).resolve().parent


def record(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator),
            "bits_display_only": -log2(x) if x else None}


def weight(matches, q=Q, total=T):
    return F(comb(matches, q), comb(total, q)) if matches >= q else F(0)


def root_family(common, copies=1):
    assert (T-common) % copies == 0
    count = 28*((T-common)//copies)
    assert 0 < count < P
    matched = common+copies
    exceptional = F(count,K-1)
    other_cap = 1024+4*(T-common)
    return {"common_fibres": common, "copies_per_polynomial": copies,
            "exceptional_nonzero_gammas": count,
            "matching_fibres_lower_bound": matched,
            "nonzero_original_candidate_agreement_upper": other_cap,
            "zero_is_unique_original_close_candidate": other_cap < 38230,
            "exceptional_gamma_probability": record(exceptional),
            "query_passing_subevent_probability_given_exception": record(weight(matched)),
            "exception_and_zero_query_subevent": record(exceptional*weight(matched)),
            "provider_width29_failure_on_exception": (
                "zero uniquely selected in original-code decoder model; full shared support fails"
                if other_cap < 38230 else
                "not established for every selected chain here; retained fixed-zero subevent only"),
            "fraction_of_2pow_minus100_budget_display_only": float(exceptional*weight(matched)*2**100),
            "warning": "Lower bound, not an upper bound on all folded cancellations or full verifier acceptance."}


def optimistic_old_budget_cap():
    old = F(336869026605739, K-1)
    target = F(1,2**100)
    low, high = 0,T
    while low < high:
        middle = (low+high+1)//2
        if old*weight(middle) <= target:
            low = middle
        else:
            high = middle-1
    assert old*weight(low) <= target < old*weight(low+1)
    return {"status": "diagnostic only; old budget NOT granted V8 applicability",
            "old_gamma_budget": record(old),
            "entire_target_budget_assigned_to_outside": record(target),
            "largest_uniform_agreement_cap_that_would_suffice": low,
            "cap_fraction_display_only": low/T,
            "at_cap": record(old*weight(low)),
            "at_next_integer": record(old*weight(low+1)),
            "other_error_terms_charged": False}


def main():
    reviewed = json.loads((HERE/"adaptive-query-package/results.json").read_text())
    for common,copies,key in [(9557,1,"original"),(9556,2,"paired")]:
        our = root_family(common,copies)["exception_and_zero_query_subevent"]
        supplied = reviewed["historical_all_zero_fibre_subevents_only"][key]
        assert F(int(our["numerator"]),int(our["denominator"])) == F(
            int(supplied["numerator"]),int(supplied["denominator"]))
    # Small exact check of the low-bin bound for arbitrary adaptive prefix weights.
    cases=0
    for total in range(1,9):
        for q in range(1,total+1):
            for cap in range(total+1):
                for m in range(cap+1):
                    assert weight(m,q,total) <= weight(cap,q,total)
                    cases+=1
    high = root_family(252843)
    assert high["nonzero_original_candidate_agreement_upper"] == 38228
    assert high["zero_is_unique_original_close_candidate"]
    result={
        "status": "query-only outside-tail obstruction; no full accepted forgery or repaired theorem",
        "prefix_event_audit": {
            "width29_failure": "depends only on words, gamma, disclosedFinal and schedule; prefix-determined in ideal full-oracle model",
            "query_phase_failure": "pointwise acceptance AND prefix-determined M<=9557",
            "fold_failure": "prefix-determined, but V7 fold relation is not automatically the V8 chord quotient",
            "list_cap_failure": "prefix-determined",
            "oracle_none": "requires actual replay/authentication/source endpoint; not renamed to a prefix event"},
        "full_degree_word_obstruction": {
            "fixed_committed_c1_word": "T_512(x); either semantic lane 0 or mask-only lane 25",
            "outside_original_code_agreement_cap": 1024,
            "initial_decoder_threshold": 38230,
            "query_matching_fibres": T,
            "query_tail_H_at_T_for_no_original_component_cover": record(F(1)),
            "experiment": "algebraic oracle/chord/query model, before semantic/relation acceptance; every legal non-aborting OOD prefix; true causal evaluations; final chosen after alpha",
            "actual_scheduler_tail_H_at_T": None,
            "literal_width29_tail_H_at_T": None,
            "nonzero_reconstruction_endpoint_residual": "gamma^lane",
            "image_relation_checks": "must reject or be bounded separately; not proved here",
            "applies_to_literal_v7_raw_fold": False,
            "full_acceptance_probability": None},
        "low_agreement_bin_universal_pointwise_upper": record(weight(9557)),
        "high_agreement_image_valid_zero_candidate_control": high,
        "original_root_control": root_family(9557),
        "paired_root_control": root_family(9556,2),
        "optimistic_old_budget_diagnostic": optimistic_old_budget_cap(),
        "tests": {"small_exact_monotonicity_cases":cases,"historical_rational_crosschecks":2},
        "source_sha256": {f:hashlib.sha256((HERE/f).read_bytes()).hexdigest()
            for f in ["adaptive_outside.rs","FullDegreeOutside.lean","adaptive_tail.py",
                      "adaptive-query-package/check_adaptive_queries.py"]},
        "new_universal_upper_bound_after_image_relation_accounting": None,
        "production_changes": False}
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
