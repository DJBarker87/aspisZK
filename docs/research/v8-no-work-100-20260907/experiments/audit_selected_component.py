#!/usr/bin/env python3
"""Audit concrete selected gamma/component proofs without replaying old leaves."""
import json
import sys
from fractions import Fraction
import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf
from audit_ordered_post_query import rational

BASE = "51b78cbf7fadee4ec70328c86add7678a43f21da"
LEAVES = [
    ("NearGammaMessageCover", "near-gamma-message-v*.log"),
    ("NearGammaSelectedC1", "near-gamma-selected-c1-v*.log"),
    ("NearGammaSelectedCoefficients", "near-gamma-selected-coefficients-v*.log"),
    ("QuotientOriginalCore", "quotient-original-core-v*.log"),
    ("SelectedQuotientOriginal", "selected-quotient-original-v*.log"),
    ("SelectedSelectorExpansion", "selected-selector-expansion-v*.log"),
    ("ComponentRows", "component-rows-v*.log"),
    ("GammaComponentGame", "gamma-component-game-v*.log"),
    ("GammaEligibility", "gamma-eligibility-v*.log"),
    ("SelectedComponentGame", "selected-component-game-v*.log"),
    ("ComponentOODBinding", "component-ood-binding-v*.log"),
    ("SelectedClaimGame", "selected-claim-game-v*.log"),
]

def result():
    evidence.BASE = BASE
    k,q,T,B = (2**31-1)**4,22,262144,2324
    local = Fraction(q+3,k-1)+Fraction(24,k)
    dense = Fraction(28,k-1)+local
    sparse = Fraction(63,k-1)+local
    assert 4*B+2 == 9298 <= 9301
    assert 5*B+255 < T
    assert dense == Fraction(53,k-1)+Fraction(24,k)
    assert sparse == Fraction(88,k-1)+Fraction(24,k)
    assert local < dense < sparse < Fraction(1,2**117)
    body = 697*16+52+24+q*621+2*296*26
    assert body == 40282
    return {
        "base_revision": BASE,
        "borrowed_formal_revision": "26a9cd4718aae9f9de7ef1c3394fb74a229085d5",
        "environment": "Lean4.32.0 / Mathlib81a5d257c8e410db227a6665ed08f64fea08e997; serialized cached focused leaves; 7GiB aggregate RSS guard; zero swaps",
        "leaves": [checked_leaf(*leaf) for leaf in LEAVES],
        "scope": "selected encoder plus causal compact field relation; not full Rust/FS acceptance or efficient payment extraction",
        "selected_reconstruction": {
            "analysis_folded_radius": B,
            "geometric_quotient_radius": 4*B,
            "deterministic_pole_symbols_max": 2,
            "deterministic_pole_fibres_max": 2,
            "reconstructed_original_radius_max": 4*B+2,
            "near_gamma_original_radius": 9301,
            "global_denominator_nonzero_assumed": False,
            "virtual_division": "total field division at unqueried poles; actual source rejecting queried poles needs acceptance coupling",
            "tuple_own_support_fibres_min": 245609,
            "tuple_own_support_symbols_min": 982436,
            "coefficient_recovery": "constructed messages, with injectivity of actual encoder; no assumed candidate membership",
            "C1_causality": "same C1-only earlyC1 optional object identified despite arbitrary late C2",
            "executable_extractor": False,
        },
        "ledger": [
            {
                "event": "fixed dense-Good prefix with a wrong individual component claim in THREE ORDINARY rows OR TWO OOD vectors AND near actual final AND compact acceptance",
                "fixing_prefix": "C1 before early challenges; C2 then fixed; tuple from C1/C2/Gamma before gamma; point weights/claims and OOD data before gamma; inactive after gamma before kappa",
                "law": "ideal uniform nonzero gamma/kappa/tau/rho, uniform field alpha0..3, fresh ordered distinct q queries",
                "bound": rational(dense),
                "terms": {"fixed_component_gamma_roots": rational(Fraction(28,k-1)),
                          "joint_image_or_shifted_rows_and_query_batch": rational(Fraction(q+3,k-1)),
                          "four_relation_repairs_once": rational(Fraction(24,k))},
                "theorem": "SelectedClaimGame.all_claims_dichotomy, dense branch",
                "coverage_input": "constructed from actual raw-message cover and pole-inclusive quotient reconstruction, not a caller recovery premise",
                "OOD_conditions": "both actual OOD coordinates on the circle; checked interpolant inverse; Data.answers and point functionals fixed before gamma; same constructed tuple for ordinary and OOD claims",
                "claim_selection": "one wrong claim chosen from the fixed prefix, not a union over145 claims or100 tuples",
            },
            {
                "event": "fixed sparse-Good prefix AND near actual final AND compact acceptance",
                "fixing_prefix": "Good from fixed C1/C2 and original-code radius9301 before gamma; all later responses causal",
                "law": "same ideal challenge law; exceptional gamma mass charged without conditioning it away",
                "bound": rational(sparse),
                "terms": {"at_most_63_good_gammas": rational(Fraction(63,k-1)),
                          "joint_image_or_shifted_rows_and_query_batch": rational(Fraction(q+3,k-1)),
                          "four_relation_repairs_once": rational(Fraction(24,k))},
                "theorem": "SelectedComponentGame.sparse_near_bound",
            },
        ],
        "composition": "Sparse/dense depends only on fixed received words. Bounds apply to their stated events; never add overlapping old near/image/row terms or call all near acceptance a failure. No 100-target union; no positive grinding credit.",
        "remaining_event_precedence": [
            "source/authentication/replay/fuel/missing-response/challenge mismatch outside current mathematical coupling",
            "actual final farther than analysis B: accepted failure of the specified extractor remains unbounded",
            "near sparse-Good branch: all compact acceptance bounded here",
            "near dense-Good branch with wrong component point claim: compact acceptance bounded here",
            "near dense-Good branch with correct point claims: enforce early semantic/copy constraints, recover and validate payment witness",
        ],
        "missing_bounds": {
            "accepted_far_final_AND_checked_witness_extraction_failure": None,
            "correct_component_claims_AND_semantic_or_payment_extraction_failure": None,
            "authenticated_C1_and_resource_bounded_oracle_replay_extraction_failure": None,
            "actual_source_acceptance_refinement": None,
            "resource_bounded_Fiat_Shamir": None,
        },
        "global_accepted_extraction_bound": None,
        "remaining_global_error_allowance": None,
        "Fiat_Shamir_ledger": {
            "bound": None,
            "resources_to_be_instantiated": ["adversary oracle queries", "transcript prequeries",
                "nonce choices and restarts", "forks and restorations", "extractor oracle/replay calls",
                "prover and extractor running time and memory"],
            "requires": "actual byte-transcript and sampler/source coupling, authenticated fixed C1 access, executable checked extraction and primitive assumptions",
            "raw_bound_is_unlimited_offline_security": False,
        },
        "payment_selector_bridge": "literal two-store descending selector expansion and high6/low4 bit split connect the selected row1014 last-pack equation to the inverse-product constraint; proof acceptance enforcing Boolean constraints still separate",
        "maximum_body_bytes": body,
        "new_proof_body_bytes": 0,
        "new_verifier_operations": 0,
        "verifier_or_production_source_changes": False,
        "new_CU_prover_or_extractor_measurement": False,
        "full_view_ZK_complete": False,
        "positive_grinding_security_credit": 0,
        "quantum_or_unlimited_offline_claim": False,
    }

if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((evidence.ROOT/"selected-component-evidence.json").read_text()) == out
        print("Selected encoder/component/C1, selector endpoint, exact ledger and current-source proof evidence match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out,indent=2))
