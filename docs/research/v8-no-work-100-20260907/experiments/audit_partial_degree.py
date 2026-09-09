#!/usr/bin/env python3
"""Evidence audit only: no unchanged Lean, Rust, SBF or rank replay."""
import json
import sys
from fractions import Fraction
import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf
import partial_fold_control

BASE = "d5507a8f247bbed7cd35591c240d8d7a40af67a0"
LEAVES = [
    ("PartialFoldRecovery", "partial-fold-recovery-v*.log"),
    ("PartialFoldSelected", "partial-fold-selected-v*.log"),
    ("PositiveResidualDegree", "positive-residual-degree-v*.log"),
]

def result():
    evidence.BASE = BASE
    control_path = evidence.EX / "partial-fold-control-output.json"
    control = json.loads(json.dumps(partial_fold_control.result()))
    assert json.loads(control_path.read_text()) == control
    known = control["QM31_optimistic_four_support_screen"]["bound"]
    screen = Fraction(int(known["numerator"]), int(known["denominator"]))
    assert Fraction(1, 2**10) < screen < Fraction(1, 2**9)
    return {
        "base_revision": BASE,
        "leaves": [checked_leaf(*leaf) for leaf in LEAVES],
        "control_source_sha256": evidence.sha(evidence.EX / "partial_fold_control.py"),
        "control_output_sha256": evidence.sha(control_path),
        "small_code_scope": control["scope"],
        "generic_factor_four_sharp": True,
        "partial_recovery": {
            "prefix": "received virtual quotient fixed before alpha0",
            "hypotheses": "four distinct alphas and supplied final-code coefficients; each actual fold differs on at most B fibres",
            "conclusion": "some full-code quotient differs from received on at most 4B complete fibres",
            "far_tail": "distance(received,full quotient code)>4B implies at most3 alphas admit any B-close final",
            "source_and_Fiat_Shamir_coupled": False,
            "image_validity_or_component_recovery_proved": False,
            "executable_rewind_extractor": False,
        },
        "conditional_pointwise_screen": control["QM31_optimistic_four_support_screen"],
        "degree_addition": {
            "new_term_individual_degree_bound": 14,
            "retained_grammar_degree": 27,
            "frozen_before_semantic_coordinate": ["message tables", "theta", "eta", "zc"],
            "scope": "source-shaped polynomial successor and MLE/selector formula, not complete Rust lowering or acceptance-to-residual theorem",
        },
        "new_Rust_or_transcript_changes": False,
        "maximum_body_bytes": 40282,
        "new_proof_or_full_transaction_measurements": False,
        "global_accepted_extraction_bound": None,
        "remaining_global_allowance": None,
        "positive_grinding_security_credit": 0,
        "remaining_events": {
            "partial_anchor_image_and_component_recovery": None,
            "all_accepted_provider_none_replay_fuel_source_authentication": None,
            "actual_semantics_to_checked_payment_witness": None,
            "actual_resource_bounded_Fiat_Shamir": None,
        },
        "adaptive_full_view_ZK_complete": False,
        "new_profile_complete_transaction_CU": None,
        "production_changes": False,
    }

if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((evidence.ROOT / "partial-degree-evidence.json").read_text()) == out
        print("Partial-fold, semantic-degree, sharp-support control and open ledger match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
