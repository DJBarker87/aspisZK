#!/usr/bin/env python3
"""Read-only verifier for the R356 diagnostic evidence bundle."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = root / "SHA256SUMS"
expected = {}
for line in manifest.read_text().splitlines():
    digest, rel = line.split("  ", 1)
    expected[rel] = digest
actual_paths = {
    p.relative_to(root).as_posix()
    for p in root.rglob("*")
    if p.is_file() and p.name != "SHA256SUMS"
}
missing = sorted(set(expected) - actual_paths)
unlisted = sorted(actual_paths - set(expected))
bad = []
for rel, digest in expected.items():
    p = root / rel
    if p.exists() and hashlib.sha256(p.read_bytes()).hexdigest() != digest:
        bad.append(rel)
summary = json.loads((root / "R356-build-summary.json").read_text())
checks = {
    "checksum_entries_match_files": not missing and not unlisted,
    "file_hashes_match": not bad,
    "build_failed_before_translation": summary["build_exit_status"] == 1 and not summary["translation_run"],
    "no_lean_result": not summary["lean_compile_run"] and summary["print_axioms"].startswith("N/A"),
}
result = {
    "status": "PASS" if all(checks.values()) else "FAIL",
    "checks": checks,
    "manifest_file_count": len(expected),
    "actual_file_count": len(actual_paths),
    "missing": missing,
    "unlisted": unlisted,
    "hash_mismatches": bad,
}
print(json.dumps(result, indent=2))
if not all(checks.values()):
    raise SystemExit(1)
