#!/usr/bin/env python3
"""Current-source proof/evidence audit; no unchanged heavy replay."""
import json
import math
import re
import sys
from fractions import Fraction
import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf
from audit_ordered_post_query import rational

BASE = "bbca32e0e30be2c489c6437dd670da164e6d852f"
LEAVES = [
    ("PreAnchorEligibility", "pre-anchor-eligibility-v*.log"),
    ("PreImageAnchor", "pre-image-anchor-v*.log"),
    ("PreImageAnchorSelected", "pre-image-anchor-selected-v*.log"),
    ("SelectedReceivedOracle", "selected-received-oracle-v*.log"),
    ("RepresentedImageGame", "represented-image-game-v*.log"),
    ("ReferenceIndependentRelation", "reference-independent-relation-v*.log"),
    ("PreAnchorJoint", "pre-anchor-joint-v*.log"),
    ("PositivePackBinding", "positive-pack-binding-v*.log"),
]

def control():
    source = evidence.EX / "pre_image_control.rs"
    good = []
    for path in evidence.EX.glob("pre-image-control-v*.log"):
        log = path.read_text()
        if f"{evidence.sha(source)}  {source}" not in log or "CONTROL_EXIT=0" not in log:
            continue
        assert "COMPILE_EXIT=0" in log and BASE in log
        assert "panicked" not in log and "AGGREGATE_RSS_STOP" not in log
        lines = [json.loads(x) for x in log.splitlines() if x.startswith('{"field":')]
        assert len(lines) == 1
        out = lines[0]
        assert out["sparse_cases"] + out["dense_cases"] == out["received_family_cases"] == 2187
        assert out["maximum_anchor_distance"] == 4
        assert out["strict_gap_counterexample"]["coverage_fails"]
        times = re.findall(r"^\s*([0-9.]+) real", log, re.M)
        rss = re.findall(r"^\s*(\d+)\s+maximum resident set size", log, re.M)
        swaps = re.findall(r"^\s*(\d+)\s+swaps$", log, re.M)
        assert len(times) == len(rss) == len(swaps) == 2
        assert all(int(x) == 0 for x in swaps)
        good.append({"output": out, "source_sha256": evidence.sha(source),
                     "log": str(path.relative_to(evidence.ROOT)), "log_sha256": evidence.sha(path),
                     "stages": [{"name": n, "exit": 0, "wall_seconds": float(t),
                                 "peak_rss_bytes": int(r), "swaps": int(s)}
                                for n,t,r,s in zip(["optimized_compile", "exact_control"],times,rss,swaps)]})
    assert len(good) == 1
    return good[0]

def result():
    evidence.BASE = BASE
    k,q,T,B = (2**31-1)**4,22,262144,2325
    sparse, image, rows = Fraction(3,k), Fraction(q+2,k-1)+Fraction(24,k), Fraction(q+3,k-1)+Fraction(24,k)
    assert 4*B == 9300 and T-5*B > 255
    assert sparse < image < rows < Fraction(1,2**118)
    assert rows-image == Fraction(1,k-1)
    # These are different events; this is an arithmetic comparison, not
    # subtraction of overlapping near/image/gamma terms in a global budget.
    old_near = Fraction(53,k-1)+Fraction(24,k)+Fraction(math.comb(9556,q),math.comb(T,q))
    body = 697*16+52+24+q*621+2*296*26
    assert body == 40282
    leaves = [checked_leaf(*leaf) for leaf in LEAVES]
    return {
        "base_revision": BASE,
        "borrowed_formal_source_revision": "26a9cd4718aae9f9de7ef1c3394fb74a229085d5",
        "environment": "Lean4.32.0/Mathlib81a5d257c8e410db227a6665ed08f64fea08e997; serialized cached leaves; 7GiB aggregate RSS guard; no dependency or SBF rebuild",
        "leaves": leaves,
        "exact_control": control(),
        "selected_geometry": {"T":T,"q":q,"example_B":B,"anchor_radius":4*B,
            "condition":"5*B+255<T", "anchor_fixed_before":"kappa/tau; chosen from R,B,alpha universe only",
            "dense_branch":"one Q represents every B-close adaptive final, and is <=4B from R on complete original fibres",
            "sparse_branch":"at most 3 alpha values admit any B-close final",
            "actual_R_constructor":"SelectedReceivedOracle.oracle, with no polynomiality assumption and analysis support D=D",
            "actual_acceptance_invariant":"ReferenceIndependentRelation.rows_accepts_iff and supported_rows_probability"},
        "ledger": [
            {"event":"sparse geometric prefix AND actual final B-close AND compact relation accepts",
             "fixing_prefix":"R and alpha set A before kappa/tau; final after alpha, before queries",
             "fresh_law":"uniform alpha in whole K, after first response; all remaining continuations causal",
             "bound":rational(sparse),"theorem":"PreAnchorJoint.sparse_near_bound","status":"formal proof complete for selected mathematical field game"},
            {"event":"dense geometric prefix AND actual final B-close AND chosen pre-challenge Q has invalid image AND compact relation accepts",
             "fresh_law":"uniform nonzero tau, whole-field alpha, uniform nonzero rho and three whole-field later alphas; fresh ordered distinct queries",
             "bound":rational(image),"terms":{"image_mix":rational(Fraction(2,k-1)),"query_batch":rational(Fraction(q,k-1)),"four_relation_repairs":rational(Fraction(24,k))},
             "theorem":"RepresentedImageGame.represented_bad_anchor_bound plus geometric identification/reference independence","status":"formal proof complete for stated represented field game"},
            {"event":"dense geometric prefix AND actual final B-close AND (invalid-image Q OR wrong shifted ordinary row of Q) AND compact relation accepts",
             "fresh_law":"add uniform nonzero kappa; Q/original rows/claims fixed beforehand",
             "bound":rational(rows),"theorem":"PreAnchorJoint.geometric_joint_dichotomy",
             "composition":"fixed image-invalid versus image-valid/wrong-row partition; uniform 3-root ceiling; all four relation repairs charged once",
             "status":"formal proof complete for selected mathematical field game, not complete verifier/FS extraction"}],
        "event_precedence": ["external/source/auth/replay layer handled separately", "sparse vs dense fixed geometry",
            "actual final B-close vs farther", "dense bad-image/row vs correct-image/rows", "specified checked witness extraction success vs failure"],
        "unbounded_terms": {"accepted_far_final_and_failed_witness_extraction":None,
            "accepted_dense_correct_image_rows_but_failed_component_or_witness_extraction":None,
            "actual_source_authentication_replay_fuel_missing_response_challenge_mismatch":None,
            "resource_bounded_Fiat_Shamir_queries_restarts_forks_extractor_time":None},
        "existing_near_gamma_bad_binding_ceiling_not_added":rational(old_near),
        "global_accepted_extraction_bound":None,"remaining_global_allowance":None,
        "positive_pack_bridge":"literal tower/Boolean selected lanes and row1014 support imply positive inverse equation from last-pack zero; semantic acceptance enforcement still separate",
        "maximum_body_bytes":body,"new_verifier_operations":0,"new_transcript_messages":0,
        "new_Rust_verifier_or_profile_changes":False,"new_full_transaction_CU_or_proving_measurements":False,
        "finite_control_runtime_is_prover_or_extractor_time":False,
        "executable_geometric_anchor_extractor":False,"adaptive_full_view_ZK_complete":False,
        "positive_grinding_security_credit":0,"quantum_or_unlimited_offline_claim":False,
        "production_changes":False,
    }

if __name__ == "__main__":
    out=result()
    if sys.argv[1:]==["--check-recorded"]:
        assert json.loads((evidence.ROOT/"pre-anchor-joint-evidence.json").read_text())==out
        print("Joint selected geometry/relation, same-word, payment-pack evidence and open ledger match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out,indent=2))
