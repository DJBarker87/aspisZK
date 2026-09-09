#!/usr/bin/env python3
"""Exact new factorial-moment checks. No field enumeration or security simulation."""
from fractions import Fraction
from itertools import combinations
from math import comb, log2
import json


def moment(T, B, m, r, t):
    return Fraction(comb(B, t) * comb(T-t, m-t), comb(T, m) * comb(r, t))


def result():
    checks = 0
    equality_cases = 0
    for T in range(1, 9):
        for B in range(T+1):
            for m in range(T+1):
                samples = list(combinations(range(T), m))
                loads = [sum(x < B for x in S) for S in samples]
                for r in range(m+1):
                    failures = sum(x >= r for x in loads)
                    for t in range(min(B, r)+1):
                        incidences = sum(comb(x, t) for x in loads)
                        assert incidences == comb(B, t)*comb(T-t, m-t)
                        assert failures*comb(r, t) <= incidences
                        e = moment(T, B, m, r, t)
                        assert Fraction(failures, len(samples)) <= e
                        equality_cases += failures*comb(r, t) == incidences
                        checks += 1
    # Why the bad support is fixed BEFORE the private sample. If adversary
    # selects bad=S after seeing S in this reduced case, failure is certain,
    # whereas the illegitimately fixed-support expression is1/2.
    assert moment(8, 4, 4, 4, 1) == Fraction(1, 2)
    T, B, m, r, t = 262144, 16535, 513, 129, 104
    e = moment(T, B, m, r, t)
    independent = Fraction(comb(m, t)*comb(B, t), comb(T, t)*comb(r, t))
    assert e == independent
    assert e < Fraction(1, 2**134)
    # No parameter sweep: fixed certificate t104 for the existing decoder.
    frontier = m*(18-10)+(1 << 10)-m
    assert frontier == 4615
    return {
        "status": "exact arithmetic verified; symbolic count is PrivateSampleMoment.failure_probability",
        "parameters": {"T":T,"common_bad_max":B,"private_sample":m,
                       "failure_threshold":r,"moment_order":t},
        "bound": {"numerator":str(e.numerator),"denominator":str(e.denominator),
                  "display_bits":log2(e.denominator)-log2(e.numerator),
                  "exact_comparison":"less than2^-134"},
        "finite_exact_checks":checks,"equality_cases":equality_cases,
        "adaptive_bad_support_falsifier":{
            "T":8,"m":4,"B":4,"r":4,"t":1,
            "illegal_post_sample_bad_equals_sample_probability":"1",
            "misapplied_fixed_support_bound":"1/2"},
        "scope":"private coefficient-decoder failure given fixed earlyC1 some and public encoder/inverse interfaces; no final-distance assumption; not payment knowledge or actual replay access",
        "law":"fresh uniform distinct513-subset, independent of fixed received C1; joint acceptance/failure counted without conditioning the law on acceptance",
        "read_model":{
            "ideal_oracle_fibres":513,"distinct_scalar_points_per_column":2052,
            "semantic_columns":16,"semantic_scalar_values_read":513*4*16,
            "semantic_M31_values_bytes_if_materialised":513*4*16*4,
            "authenticated_full_C1_leaf_value_bytes":403,"salt_bytes_per_leaf":32,
            "optional_extra_bundle_frontier_max":frontier,
            "optional_extra_bundle_bytes_without_predetermined_ids":513*435+frontier*26,
            "optional_extra_bundle_bytes_with_u32_ids":513*439+frontier*26,
            "bundle_status":"cost model only; extra extractor oracle, not provided by the proof or Merkle root",
            "q22_transcript_count_information_floor":24,
            "actual_replay_calls":None,"actual_replay_failure_bound":None,
            "actual_extractor_time_or_memory":None},
        "body_bytes":697*16+52+24+22*621+2*296*26,
        "extra_proof_bytes":0,"extra_verifier_queries":0,
        "actual_private_sampler_refined":False,"sampler_exhaustion_in_this_theorem":False,
        "old_137bit_hypergeometric_bound":"existing arithmetic only, reused unchanged; new kernel moment bound is deliberately weaker",
        "global_security_bound":None,"grinding_credit_bits":0,
    }


if __name__ == "__main__":
    print(json.dumps(result(), indent=2))
