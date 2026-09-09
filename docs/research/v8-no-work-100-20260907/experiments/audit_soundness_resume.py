#!/usr/bin/env python3
"""Reuse exact local ledgers; never turn conditional terms into global security."""
from fractions import Fraction
from pathlib import Path
from math import comb
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent.parent
BASE = "f021007879dcd9e2bca795b4758e187fa1c3b302"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rational(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def results():
    near = json.loads((ROOT / "near-gamma-results.json").read_text())
    sampling = json.loads((ROOT / "c1-sampling-results.json").read_text())
    performance = json.loads((ROOT / "terminal-query-results.json").read_text())
    k = (2**31 - 1)**4
    e_near = Fraction(53, k-1) + Fraction(24, k) + Fraction(comb(9556, 22), comb(262144, 22))
    assert e_near == Fraction(int(near["local_max_bound"]["numerator"]),
                              int(near["local_max_bound"]["denominator"]))
    e_tail = Fraction(int(sampling["sample_tail_numerator"]),
                      int(sampling["sample_tail_denominator"]))
    # Reuse the recorded exact hypergeometric result, not a fresh parameter sweep.
    assert e_tail + Fraction(1, 2**28160) < Fraction(1, 2**137)
    assert 2*245609 - 262144 == 229074 > 256
    assert 4*128 == 512 <= (4*513 - 1025)//2 == 513 < 4*129
    assert 697*16 + 52 + 24 + 22*621 + 2*296*26 == 40282
    local = e_near + Fraction(1, 2**137)
    assert local < Fraction(1, 2**100)
    assert performance  # Full measured evidence stays in the pinned CU ledger.
    return {
        "base_revision": BASE,
        "status": "conditional local arithmetic; no numerical global certificate",
        "target": "Pr[A and specified resource-bounded extractor fails to return a checked payment witness]",
        "profile": {"field": "QM31", "q": 22, "domain": 1048576,
                    "maximum_body_bytes": 40282, "new_protocol_bytes": 0,
                    "new_verifier_operations": 0, "grinding_credit_bits": 0},
        "early_C1": {"columns": 26, "minimum_own_support_fibres": 245609,
                     "formal_status": "generic uniqueness and total optional construction proved; concrete identification and late-C2 instantiation unresolved",
                     "two_support_intersection_minimum": 229074,
                     "distinct_original_codewords_overlap_cap": 256,
                     "none_branch": "no tuple meets this support threshold; not extraction impossibility",
                     "algorithmic_status": "mathematical optional object; computability/resource theorem separate"},
        "common_sample": {"semantic_columns": 16, "fibres": 513,
                          "scalar_samples_per_column": 2052,
                          "ambient_polynomial_dimension": 1025,
                          "correctable_scalar_errors": 513,
                          "failure_requires_bad_sample_fibres_at_least": 129,
                          "column_union_multiplier": 1,
                          "law": "independent ideal private uniform sampling; not fixed SHA test coins"},
        "supported_local_terms": [
            {"event": "restricted near-anchor false component-point binding",
             "fixing_prefix": "received C1/C2 and point/OOD claims before gamma; inactive before kappa",
             "bound": rational(e_near),
             "applicability": "existing modular causal theorem; complete optimized-source constructor still required",
             "overlap": "already includes all four degree-six relation repairs; do not add image or row totals again"},
            {"event": "private common-sample coefficient recovery failure or sampler exhaustion GIVEN a fixed close C1 tuple",
             "fixing_prefix": "C1 word and early tuple before independent private extractor coins",
             "upper_bound": rational(Fraction(1, 2**137)),
             "applicability": "exact prior sampling arithmetic plus new deterministic all-column Gao interface; actual source/sampling/refinement still required",
             "overlap": "one shared bad-fibre set; no factor16; independent extractor step, not extra proof queries"}
        ],
        "conditional_two_event_union_ceiling_only": rational(local),
        "headroom_after_only_that_conditional_union": rational(Fraction(1, 2**100)-local),
        "composition_warning": "These two events are not a cover of A and not X. The arithmetic is not a global theorem or available release budget.",
        "remaining": {
            "accepted_uncovered_or_far_C1_recovery_failure": None,
            "accepted_coefficient_correct_but_payment_witness_failure": None,
            "actual_source_to_causal_game_correspondence": None,
            "authenticated_oracle_access_and_replay_failures": None,
            "bounded_decoder_Rust_refinement_and_runtime": None,
            "Fiat_Shamir_query_retry_fork_runtime_bound": None,
            "full_view_zero_knowledge": None,
            "global_remaining_allowance": None,
            "global_security_bits": None
        },
        "reused_evidence_sha256": {name: digest(ROOT/name) for name in
            ["near-gamma-results.json", "c1-sampling-results.json",
             "gao-recovery-evidence.json", "terminal-query-results.json"]}
    }


if __name__ == "__main__":
    result = results()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((ROOT / "soundness-resume-ledger.json").read_text()) == result
        print("Exact local ledger matches; global accepted-extraction bound remains explicitly missing.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(result, indent=2))
