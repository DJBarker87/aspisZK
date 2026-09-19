#!/usr/bin/env python3
"""Audit the archived V8 q22 slice without mistaking it for source closure.

This is intentionally a source-text/provenance audit.  It establishes the
literal grammar visible in the checked-in historical files and records the
reconstructed transformed performance images. It does not execute the generated
host, prove a random-oracle law, or assert that this archived harness was the
sole publication path.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from reconstruct_generated_inputs import transform_performance, transform_performance_v4


ROOT = Path(__file__).resolve().parents[4]
ARCHIVE = ROOT / "docs/research/v8-positive-complete-devnet-20260909"
RELATION = ARCHIVE / "upstream/relation_callback.rs"
PERFORMANCE = ARCHIVE / "upstream/performance.rs"
LIVE_CONTEXT = ARCHIVE / "live_context.rs"
INTEGRATION = ARCHIVE / "evidence/integration-inputs-v4.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contains_in_order(text: str, *needles: str) -> bool:
    cursor = 0
    for needle in needles:
        cursor = text.find(needle, cursor)
        if cursor < 0:
            return False
        cursor += len(needle)
    return True


def main() -> None:
    integration = json.loads(INTEGRATION.read_text())
    performance_entry = integration[
        "docs/research/v8-no-work-100-20260907/experiments/performance.rs"
    ]
    relation_entry = integration[
        "docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs"
    ]
    relation = RELATION.read_text()
    performance = PERFORMANCE.read_text()

    actual_relation = sha256(RELATION)
    actual_performance = sha256(PERFORMANCE)
    assert actual_relation == relation_entry["after"]
    assert actual_performance == performance_entry["before"]
    assert actual_performance != performance_entry["after"]
    reconstructed = transform_performance(performance)
    reconstructed_hash = hashlib.sha256(reconstructed.encode()).hexdigest()
    initial_entry = json.loads((ARCHIVE / "integration-inputs.json").read_text())[
        "docs/research/v8-no-work-100-20260907/experiments/performance.rs"
    ]
    assert reconstructed_hash == initial_entry["after"]
    assert reconstructed_hash != performance_entry["after"]
    v4 = transform_performance_v4(performance)
    v4_hash = hashlib.sha256(v4.encode()).hexdigest()
    for version in range(1, 5):
        entry = json.loads((ARCHIVE / f"evidence/integration-inputs-v{version}.json").read_text())[
            "docs/research/v8-no-work-100-20260907/experiments/performance.rs"
        ]
        assert v4_hash == entry["after"]
    assert contains_in_order(v4,
        'assert!(std::env::var_os("ASPIS_V8_MAX_FRONTIER_SCAN").is_none());',
        'for seed in seeds {')
    assert v4.count('std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();') == 2
    assert 'StateOnlyAttemptSecrets::deterministic_spend_fixture([seed;32],[seed+1;32],[seed+2;32])' in v4
    assert 'InMemoryStateOnlyMaskNonceStore::default()' in v4
    assert 'generate_for_mask_nonce' not in v4
    live = LIVE_CONTEXT.read_text()
    # Equal to the blob at the selected SOURCE_MANIFEST target 9e432896.
    assert sha256(LIVE_CONTEXT) == '6c71cdf5e5677761b638e8532981ca7f75b1387475b31d821bf4775431780bd2'
    assert 'let key = dig(10); let salt = dig(100);' in live
    assert 'single_output(leaf).unwrap(), selected_second: false' in live
    assert contains_in_order(
        reconstructed,
        'assert!(std::env::var_os("ASPIS_V8_MAX_FRONTIER_SCAN").is_none());',
        'for seed in seeds {',
    )
    assert reconstructed.count('std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();') == 2

    assert contains_in_order(
        relation,
        "fn query_schedule(p:&mut Prefix,finals:&[K],nonces:&[u8])",
        "p.t.absorb(label::V6_FINAL256,&bytes(finals));",
        "p.t.absorb(label::GRIND_NONCE,&nonces[16..24]);",
        "p.t.challenge_queries_without_replacement(22,1<<18,64)",
        'p.t.absorb(label::PROFILE,b"AV8/query-batch/v1");',
        "let rho=sample(&mut p.t,true)?",
    )
    assert contains_in_order(
        performance,
        'let Some(cap)=std::env::var("ASPIS_V8_MAX_FRONTIER_SCAN").ok() else{',
        "let(q,rho)=query_schedule(p,finals,&nonce).unwrap();return(q,rho,nonce,0);",
    )
    assert contains_in_order(
        performance,
        "for attempt in 0..cap {",
        "if frontier==296 {",
        "return(q,rho,nonce,attempt+1);",
    )
    assert contains_in_order(
        performance,
        "let(queries,rho,nonces,stress_attempts)=stress_queries(&mut p,&finals);",
        'std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();',
    )

    print(
        json.dumps(
            {
                "audit": "r15_archived_q22_source_slice",
                "relation_callback_sha256": actual_relation,
                "performance_sha256": actual_performance,
                "initial_transformed_image": {
                    "sha256": reconstructed_hash,
                    "matches_initial_manifest": True,
                    "matches_v4_manifest": False,
                    "stress_environment_rejected": True,
                    "proof_file_sinks": 2,
                    "negative_controls_write_before_continue": True,
                },
                "v4_transformed_image": {
                    "sha256": v4_hash,
                    "matches_all_four_evidence_manifests": True,
                    "delta_from_initial": "delete obsolete pre-rebind statement assertion",
                    "stress_environment_rejected": True,
                    "proof_file_sinks": 2,
                },
                "experiment_boundary": {
                    "private_entropy": "fixed repeated-byte fixture seeds",
                    "nonce_reservation": "in-memory demo store",
                    "live_context_sha256": sha256(LIVE_CONTEXT),
                    "live_witness": "fixed note secrets, single output, selected_second=false",
                    "implements_intended_entropy_backed_two_witness_game": False,
                },
                "query_grammar": {
                    "query_count": 22,
                    "domain": 262144,
                    "draw_limit": 64,
                    "final256_before_nonce_before_queries": True,
                    "rho_after_queries": True,
                },
                "default_path": "one direct schedule; no frontier selection",
                "environmental_stress_path": (
                    "ASPIS_V8_MAX_FRONTIER_SCAN can search nonce suffixes "
                    "until frontier == 296"
                ),
                "publication_slice": "writes proof-{seed}.bin after schedule use",
                "closure": {
                    "complete": False,
                    "reason": (
                        "both host images are authenticated; the complete "
                        "generated build, entropy-backed adapter, shared-oracle "
                        "law and public-event refinement remain unproved"
                    ),
                    "expected_performance_after_sha256": performance_entry["after"],
                },
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
