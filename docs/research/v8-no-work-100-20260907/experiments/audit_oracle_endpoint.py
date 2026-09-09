#!/usr/bin/env python3
"""Audit new causal/endpoint results without rerunning unchanged heavy jobs."""
import json
import re
import sys

import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf

BASE = "bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee"
LEAVES = [
    ("EarlyC1OracleMachine", "early-c1-oracle-machine-v*.log"),
    ("EarlyC1OracleGame", "early-c1-oracle-game-v*.log"),
    ("InterleavedChordLinear", "interleaved-chord-linear-v*.log"),
    ("InterleavedChordAlgebra", "interleaved-chord-algebra-v*.log"),
    ("InterleavedChordPair", "interleaved-chord-pair-v*.log"),
    ("InterleavedChordFull", "interleaved-chord-full-v*.log"),
    ("InterleavedChordRows", "interleaved-chord-rows-v*.log"),
    ("SelectedTransferPositive", "selected-transfer-positive-v*.log"),
]


def rust_log(relative, sources, markers):
    path = evidence.ROOT / relative
    log = path.read_text()
    assert BASE in log
    assert not re.search(r"^error(?:\[|:)|panicked at|AGGREGATE_RSS_STOP|^EXIT=[1-9]", log, re.M)
    assert "EXIT=0" in log
    for source in sources:
        file = evidence.EX / source
        assert f"{evidence.sha(file)}  {file}" in log, source
    for marker in markers:
        assert marker in log, marker
    stages = []
    for wall, rss, swaps in re.findall(
        r"([0-9.]+) real.*?\n\s*(\d+)\s+maximum resident set size.*?\n\s*(\d+)\s+swaps", log, re.S
    ):
        assert int(swaps) == 0
        stages.append({"wall_seconds": float(wall), "peak_rss_bytes": int(rss), "swaps": int(swaps)})
    assert stages
    return {"log": relative, "sha256": evidence.sha(path), "exit": 0, "stages": stages}


def result():
    evidence.BASE = BASE
    body = {"fixed_canonical_fields": 697*16, "roots": 52, "nonces": 24,
            "query_records": 22*621, "maximum_frontiers": 2*296*26}
    assert sum(body.values()) == 40282
    return {
        "base_revision": BASE,
        "v7_lazy_oracle_import_pin": "26a9cd4718aae9f9de7ef1c3394fb74a229085d5",
        "leaves": [checked_leaf(name, pattern) for name, pattern in LEAVES],
        "scope": "kernel-checked model/algebraic interfaces, optimized actual-source controls and an endpoint falsifier; not full Rust/SBF/FS refinement",
        "rust_evidence": {
            "prefix_controls": rust_log("evidence/early-c1-trace-controls-v1.log", ["early_c1_trace.rs"],
                ["test result: ok. 3 passed; 0 failed"]),
            "same_payment_prefix": rust_log("evidence/early-c1-trace-payment-v1.log",
                ["early_c1_trace.rs", "performance.rs", "relation_callback.rs"],
                ["EARLY_C1_TRACE raw=1051764 unique=789620 input_bytes=238287374 verifier_calls=2812 accepted_openings=22 path_memberships=418 pre_lambda_chi=true actual_answers=true resolver_hash_calls=0 raw_trace_persisted=false",
                 '"body_bytes":39502', '"stress_nonce_attempts":0']),
            "selected_zero_outputs": rust_log("evidence/selected-transfer-zero-v3.log",
                ["selected_transfer_zero.rs", "recovered_witness.rs"],
                ["baseline=valid rewritten_trace_exact=true all_zero_residuals=18089 compiled_boolean_rows=1024",
                 "case=recipient_zero public_valid=true all_zero_residuals=18089 compiled_boolean_rows=1024 decode_ok=true validator=Conservation extracted_checked=reject",
                 "case=change_zero public_valid=true all_zero_residuals=18089 compiled_boolean_rows=1024 decode_ok=true validator=Conservation extracted_checked=reject"]),
        },
        "ideal_oracle_term": {
            "classical_only": True,
            "event": "later new raw input in actual model log hits a pre-prefix C1 unresolved target",
            "fixing_prefix": "initial full256 answer records and C1 root, before arbitrary adaptive continuation",
            "fresh_law": "full256 uniform fresh-answer tape; cached outputs reused, full tail visible to strategy",
            "resources": "at most steps total query opportunities and Q fresh calls; halt/exhaustion explicit",
            "target_count": 262144,
            "full256_target_preimage_cap": str(262144 * 2**48),
            "probability_expression_positive_steps": "Q * 262144 / 2^208",
            "reduced_per_fresh_query_rational": {"numerator": "1", "denominator": str(2**190)},
            "source_status": "honest actual-answer trace control executed; universal V8 strategy/refinement/replay resource coupling unresolved",
            "overlap": "one whole-domain target event, not a per-opening q22 union; shared raw collision separate",
        },
        "selected_payment_obstruction": {
            "refuted": "all current selected residuals zero implies this decoder's selected compiler endpoint accepts",
            "counterexamples": "recipient/change 0/1000 and 1000/0 with genuine fixed input/path and regenerated exact outputs/append",
            "does_not_establish": ["PCS or complete transaction acceptance", "absence of another valid witness", "violation of older generic relation allowing hidden zero amounts"],
            "repair_control": "one product-inverse residual at existing conservation row with row1014c3 reserved",
            "installed": False,
            "mask_cells_if_installed": {"old": 3803, "new": 3802},
            "remaining": "full selected-source integration, packed lane94/table identity, hiding, theorem bridges, honest producer and matched CU before adoption",
        },
        "remaining_accepted_mass": [
            {"event": "shared raw208 collision", "bound": None, "needs": "actual total distinct-query resources and shared causal hash composition"},
            {"event": "near-regime acceptance with failed checked extraction", "bound": None, "needs": "applicable near-gamma/source constructor plus executable recovery and full selected endpoint"},
            {"event": "accepted outside/far/none/replay/fuel/mismatch executions", "bound": None, "needs": "total bounded extractor coupling; radius failure is not itself extraction failure"},
            {"event": "scalar acceptance with failed pointwise consistency", "bound": None, "needs": "compose actual shifted query/row games without double-counted relation repairs"},
        ],
        "body_sections_bytes": body,
        "maximum_body_bytes": sum(body.values()),
        "actual_trace_body_bytes": 39502,
        "new_SBF_CU_measurements": False,
        "performance_reference_worst_measured_complete_CU": 1047041,
        "performance_scope": "prior frozen four-shape comparison, not universal and not the instrumented host run",
        "global_accepted_extraction_bound": None,
        "remaining_global_allowance": None,
        "full_view_zero_knowledge_complete": False,
        "resource_bounded_FS_complete": False,
        "positive_grinding_credit": 0,
        "production_changes": False,
    }


if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((evidence.ROOT / "oracle-endpoint-evidence.json").read_text()) == out
        print("Current-source oracle/endpoint evidence, exact body and unresolved ledger match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
