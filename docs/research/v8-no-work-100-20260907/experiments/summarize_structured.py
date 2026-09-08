#!/usr/bin/env python3
"""Reconcile measured CU logs. Integers only; never extrapolate pool CU."""
import json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FILES = {
    "structured": "structured-svm.log",
    "qm31_batch_rejected": "structured-svm-k.log",
    "base_batch": "structured-svm-m.log",
    "tower_mixed_prepared": "structured-svm-kernels.log",
    "final_profile": "structured-final-profile-svm.log",
    "final_quiet": "structured-final-quiet-svm.log",
    "semantic_duplicate_control": "structured-semantic-svm.log",
    "fused_rows": "structured-fused-svm.log",
    "cached_points_block_horner": "structured-horner-svm.log",
    "packed_gamma": "structured-gamma-svm.log",
    "shared_gamma": "structured-reuse-svm.log",
    "grouped_linear": "structured-grouped-svm.log",
    "shared_query": "structured-query-shared-svm.log",
    "best_checked_quiet": "structured-best-quiet-svm.log",
    "blanket_overflow_off_control_NOT_SELECTED": "structured-overflow-control-svm.log",
    "core_only_overflow_off_control_NOT_SELECTED": "structured-core-overflow-control-svm.log",
}
def read_rows(path):
    rows = [json.loads(x) for x in path.read_text().splitlines() if x.startswith("{")]
    assert len(rows) in (18,33), (path, len(rows))
    assert all(x["unchanged_accounts"] for x in rows)
    assert all(x["accepted"] == (x["case"] == "honest")
               for x in rows if x["cu_limit"] == 100000000)
    assert all("Custom(" in x["error"] for x in rows
               if x["cu_limit"] == 100000000 and x["case"] != "honest")
    return rows
def stages(row):
    out, name, previous = {}, None, 100000000
    for line in row["logs"]:
        if line.startswith("Program log: v8:"):
            name = line.removeprefix("Program log: ")
        match = re.fullmatch(r"Program consumption: (\d+) units remaining", line)
        if match and name is not None:
            left = int(match[1]); out[name] = previous - left
            previous = left; name = None
    if not out:
        return None
    out["exit_and_driver"] = row["cu"] - (100000000 - previous)
    assert sum(out.values()) == row["cu"]
    return out
variants = {}
for key, file in FILES.items():
    rows = read_rows(ROOT / "evidence" / file)
    honest = [x for x in rows if x["accepted"] and x["cu_limit"] == 100000000]
    variants[key] = {
        "evidence": "evidence/" + file,
        "honest_cu": [x["cu"] for x in honest],
        "ordinary_limit_honest_accepts": [x["accepted"] for x in rows
                                         if x["cu_limit"] == 1400000],
        "stage_cu_seed1": stages(honest[0]),
        "malformed_checked_rejections": sum(x["case"] != "honest" for x in rows),
        "full_transaction_cu": None,
    }
body = 697*16 + 52 + 24 + 22*621 + 2*296*26
assert body == 40282
best = variants["best_checked_quiet"]["honest_cu"]
prover_log=(ROOT/"evidence/structured-prover-final.log").read_text()
prover_events=[json.loads(line[5:]) for line in prover_log.splitlines() if line.startswith("PERF ")]
prover_times=[row["seconds"] for row in prover_events if row.get("phase")=="prover_total_excludes_setup"]
assert len(prover_times)==3
prover_setup=next(row["seconds"] for row in prover_events if row.get("phase")=="setup_compiler_encoder_matrix")
prover_rss=int(re.search(r"Maximum resident set size \(kbytes\): (\d+)",prover_log)[1])
prover_swap=int(re.search(r"Swaps: (\d+)",prover_log)[1])
assert [row["body_bytes"] for row in prover_events if row.get("accepted")]==[39502,39606,39606]
out = {
    "schema": "aspis.v8.structured-performance.v2",
    "base_revision": "9e57493dbba8fb01c50bd62f737f187006a33cb1",
    "scope": "isolated verifier; no account authentication or pool settlement",
    "reference_cu": [7312575,7317164,7321343],
    "variants": variants,
    "wire": {"max_body_bytes": body, "actual_body_bytes": [39502,39606,39606],
             "new_proof_claims": 0, "new_nonce_bytes": 0, "new_rounds": 0},
    "prover": {
        "evidence": "evidence/structured-prover-final.log",
        "seconds_excluding_setup": prover_times,
        "setup_seconds": prover_setup, "process_peak_rss_kib": prover_rss,
        "process_wall_seconds": 13.49, "swap": prover_swap, "search_attempts": 0,
        "p95_seconds": None, "p99_seconds": None,
        "dense_committed_columns_bytes": (26*4+3*16)*2**20,
        "full_proving_network_traffic_bytes": 0,
    },
    "transcript": {
        "version": "AV8/functional/three-MLE-grouped64/chord/v2",
        "verifier_derived_description_bytes": 545,
        "previous_expanded_weight_bytes": 16384,
        "byte_identical_to_old_transcript": False,
        "same_v2_proof_bytes_across_arithmetic_variants": True,
    },
    "selected_excess_over_1400000": [n-1400000 for n in best],
    "measured_matched_v7_complete_cu": None,
    "complete_transaction_parity": "not established",
    "full_security_bits": None,
    "unresolved": ["global recovery/payment knowledge", "full-view ZK",
                   "resource-bounded FS with nonce/retry selection",
                   "source refinement", "matched complete-transaction CU"],
}
print(json.dumps(out, indent=2))
