#!/usr/bin/env python3
"""Read-only integrity and primary-receipt verifier for the R356 bundle."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = root / "SHA256SUMS"
entries = {}
for line in manifest.read_text().splitlines():
    digest, rel = line.split("  ", 1)
    entries[rel] = digest
actual_paths = {
    p.relative_to(root).as_posix()
    for p in root.rglob("*")
    if p.is_file() and p != manifest
}
missing = sorted(set(entries) - actual_paths)
unlisted = sorted(actual_paths - set(entries))
bad = []
for rel, digest in entries.items():
    p = root / rel
    if p.exists() and hashlib.sha256(p.read_bytes()).hexdigest() != digest:
        bad.append(rel)

base = root / "r356-comment-names-candidate"
build = base / "build-evidence/4dc195a7537d-20261002T120840Z"
launch = base / "history/launch-4dc195a7537d-20261002T120840Z"
result = json.loads((build / "build-result.json").read_text())
command = json.loads((build / "build-command.json").read_text())
receipt = json.loads((launch / "launch-receipt.json").read_text())
launch_result = json.loads((launch / "launch-result.json").read_text())
clone = json.loads((build / "clone-audit.json").read_text())
pristine_runner = launch / "run_cached_build-before-revision-capture.py"
materialized_runner = build / "run_cached_build.py"
reservation_after = json.loads((build / "build-host-reservation-after.json").read_text())
cgroup_samples = json.loads((build / "cgroup-samples.json").read_text())
gnu_time = (build / "compiler-gnu-time.txt").read_text()
docker_time = (build / "docker-cli-time.txt").read_text()
build_log = (build / "build.log").read_text()

launch_revision = "4dc195a7537d01ddb2ffd139c2a1d79fd836a847"
source_revision = "56a931fc3879354a2fa584e73bd0a1d412714851"
binary_sha = "dc4b9d209c645a0d951bdd78f7e0f9d6fb9d09b0e88491edded1ee7beb791cd6"
candidate_source_sha = "8da73e4510c8c7e579d959dc299243a91fc3fa9ae606969f8c8f5fd411b8e990"
candidate_extract_sha = "2893509bb9fbbc159e9262532adab1d2b4f684b269f4e835d8cf5b6709188ddf"
checks = {
    "pristine_and_materialized_runner_hashes_match_record": hashlib.sha256(pristine_runner.read_bytes()).hexdigest() == "65b1effb942f069a3b1866471713118547899304fa755b613b42e96a7edd3a96" and hashlib.sha256(materialized_runner.read_bytes()).hexdigest() == receipt.get("runner_sha256_after_revision_capture"),
    "checksum_entries_match_files": not missing and not unlisted,
    "file_hashes_match": not bad,
    "launch_revision_matches_primary_receipts": all(x.get("launch_revision", x.get("launch_revision_captured_at_launch")) == launch_revision for x in (result, command, receipt, launch_result)),
    "source_parent_identity_matches_primary_receipts": result.get("source_revision_of_R349_candidate") == source_revision and command.get("source_revision_of_R349_candidate") == source_revision,
    "cached_parent_binary_identity_matches_primary_receipts": receipt.get("parent_R349_binary_sha256") == binary_sha and result.get("candidate_source_tree_sha256_before_build") == candidate_source_sha,
    "candidate_source_hash_matches_primary_receipt": result.get("candidate_ExtractTypes_sha256") == candidate_extract_sha and command.get("R356_ExtractTypes_sha256") == candidate_extract_sha,
    "clone_audit_confirms_one_changed_source_and_zero_shared_inodes": clone.get("only_ExtractTypes_changed") is True and clone.get("shared_regular_file_inodes") == 0 and clone.get("candidate_cached_executable_matches_R349") is True,
    "build_failure_status_matches_primary_records": result.get("build_exit_status") == 1 and launch_result.get("launcher_exit_status") == 1 and "Error: This expression has type" in build_log and 'extract/ExtractTypes.ml", line 1253' in build_log,
    "exact_type_mismatch_is_present": 'ctx.trans_ctx' in build_log and 'expected of type' in build_log and 'extraction_ctx' in build_log,
    "no_binary_translation_or_lean_run_matches_primary_record": result.get("binary_exists") is False and result.get("translation_or_Lean_compile_run") is False,
    "GNU_time_status_and_rss_are_from_compiler_record": "Maximum resident set size (kbytes): 283756" in gnu_time and "Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.29" in gnu_time and "Exit status: 1" in gnu_time,
    "Docker_CLI_RSS_is_labeled_parent_only": command.get("docker_cli_time_rss_label", "").startswith("Docker CLI parent-process RSS only" ) and "Maximum resident set size (kbytes): 27808" in docker_time,
    "cgroup_peak_matches_samples_and_has_no_swap_or_oom": max(int(s.get("memory.peak", "0")) for s in cgroup_samples["samples"] if "memory.peak" in s) == result.get("sampled_container_memory_peak_bytes") and result.get("sampled_container_memory_swap_peak_bytes") == 0 and "MemorySwapPeak=0" in reservation_after["R356_slice_after"] and all("oom_kill 0" in s.get("memory.events", "") for s in cgroup_samples["samples"] if "memory.events" in s),
    "prior_R351_failure_is_retained_in_R352_preflight": (root / "r352-comment-emission-preflight/R351-translate.log").exists() and json.loads((root / "r352-comment-emission-preflight/R351-result.json").read_text()).get("exit_status") == 2 and "NameMatcher" in (root / "r352-comment-emission-preflight/R351-translate.log").read_text(),
}
report = {
    "status": "PASS" if all(checks.values()) else "FAIL",
    "checks": checks,
    "manifest_file_count": len(entries),
    "actual_file_count": len(actual_paths),
    "missing": missing,
    "unlisted": unlisted,
    "hash_mismatches": bad,
    "primary_receipt_values": {
        "launch_revision": launch_revision,
        "R349_source_revision": source_revision,
        "R349_binary_sha256": binary_sha,
        "build_exit_status": result.get("build_exit_status"),
        "compiler_GNU_time_wall_seconds": 1.29,
        "compiler_GNU_time_max_rss_kib": 283756,
        "Docker_CLI_parent_RSS_kib": 27808,
        "sampled_container_cgroup_peak_bytes": result.get("sampled_container_memory_peak_bytes"),
    },
}
print(json.dumps(report, indent=2))
if not all(checks.values()):
    raise SystemExit(1)
