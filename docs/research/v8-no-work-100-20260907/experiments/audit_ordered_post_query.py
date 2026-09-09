#!/usr/bin/env python3
"""Check retained leaf evidence and the exact, restricted post-query ledger.

No prover/verifier benchmark or probabilistic experiment is run here.
"""
import json
import math
import re
import sys
from decimal import Decimal, localcontext
from fractions import Fraction

import audit_soundness_proofs as evidence

BASE = "5e26df14ad5fc674d5ea43d02431f1dc9ef682fa"
LEAVES = [
    ("PostQueryFunctional", "post-query-lean-v*.log"),
    ("OrderedQueryGame", "ordered-query-lean-v*.log"),
    ("OrderedPostQueryGame", "ordered-post-query-lean-v*.log"),
    ("SelectedPairDecoder", "selected-pair-leaf-v*.log"),
    ("EarlyC1Identification", "early-c1-identification-v*.log"),
]


def rational(value):
    with localcontext() as context:
        context.prec = 80
        bits = -(Decimal(value.numerator) / Decimal(value.denominator)).ln() / Decimal(2).ln()
    return {"numerator": str(value.numerator), "denominator": str(value.denominator),
            "display_bits_not_certificate": str(bits)}


def result():
    evidence.BASE = BASE
    leaves = []
    for name, pattern in LEAVES:
        source = (evidence.EX / (name + ".lean")).read_text()
        assert not re.search(r"^\s*(?:axiom\s|sorry\b|admit\b)", source, re.M)
        leaves.append(evidence.final_leaf(name, pattern))
    k, q, domain, radius, degree = (2**31 - 1)**4, 22, 262144, 9301, 255
    miss = Fraction(math.comb(radius + degree, q), math.comb(domain, q))
    rho, tail = Fraction(q, k - 1), Fraction(18, k)
    post = miss + rho + tail
    near = Fraction(53, k - 1) + Fraction(24, k) + miss
    assert near - post == Fraction(31, k - 1) + Fraction(6, k)
    body = 697*16 + 52 + 24 + q*621 + 2*296*26
    assert body == 40282
    return {
        "base_revision": BASE,
        "scope": "kernel-checked field/source-shaped post-query and decoder interfaces; not translated Rust acceptance or global soundness",
        "environment": "Lean4.32.0; Mathlib81a5d257c8e410db227a6665ed08f64fea08e997; serialized focused cached leaves",
        "leaves": leaves,
        "early_C1_scope": "Only agreement_cap_from_sets, matching_set_cap and exact_agreement_cap are retained checked declarations; the optional-object identify application remains unverified in an explicit draft after guarded resource failures.",
        "claim_regime": "ideal classical raw local game; neither a quantum claim nor resource-independent non-interactive security",
        "profile": {"field_cardinality": str(k), "q": q, "domain_fibres": domain,
                    "illustrative_radius": radius, "final_degree_cap": degree,
                    "maximum_body_bytes": body, "positive_grinding_credit_bits": 0},
        "post_query_event": {
            "fixing_prefix": "after response0/alpha0/final; reference Q and received folded function fixed before fresh ordered queries",
            "geometry_hypothesis": "received equals Eval(Fold(Q)) on D outside an explicit set B",
            "bad_prefix": "actual carried reference discrepancy nonzero OR actual final differs from Fold(Q)",
            "acceptance": "the modeled compact three-round raw tail accepts",
            "fresh_law": "uniform ordered distinct q schedule, then uniform nonzero rho, then sequential uniform field alpha1..3",
            "adaptive_responses": "raw tail may depend on full ordered schedule and rho, then each previous relation challenge",
            "event_precedence": "wrong reference first; if reference correct then different final; the same uniform conditional bound holds on both disjoint classes",
            "theorems": ["OrderedPostQueryGame.wrong_reference_bound", "OrderedPostQueryGame.different_final_bound"],
            "status": "formal proof complete for the stated constructed field game",
            "terms": [
                {"event": "different final matches received on all ordered queries", "bound": rational(miss)},
                {"event": "nonzero shifted degree-q discrepancy cancels at rho", "bound": rational(rho)},
                {"event": "a remaining discrepancy is repaired by three degree-six rounds", "bound": rational(tail)}],
            "conditional_upper_bound": rational(post),
            "support_existence_from_acceptance": None,
            "source_sampler_and_FS_transfer": None,
            "overlap": "All three terms are already present in the near/image relation-game accounting; this is not a new additive global charge. First relation round is outside this post-alpha0 game."},
        "existing_near_ceiling_arithmetic_only": rational(near),
        "global_accepted_extraction_bound": None,
        "remaining_global_numerical_allowance": None,
        "unsupported_obligations": {
            "accepted_uncovered_recovery_including_far_regimes": None,
            "early_C1_semantic_copy_binding": None,
            "remaining_tuple_to_payment_and_context_bridge": None,
            "authentication_access_replay_abort_fuel_and_provider_none": None,
            "complete_repaired_source_refinement": None,
            "resource_bounded_Fiat_Shamir": None,
            "full_view_ZK_simulation": None},
        "new_verifier_operations": 0,
        "new_proof_messages_or_bytes": 0,
        "new_CU_proving_or_extraction_measurements": False,
        "production_changes": False}


if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((evidence.ROOT / "ordered-post-query-evidence.json").read_text()) == out
        print("Current-source leaf evidence, standard axioms, exact local ledger and 40,282-byte census match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
