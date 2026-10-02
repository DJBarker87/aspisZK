#!/usr/bin/env python3
"""Offline integrity check for the saved R374 evidence bundle."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit("FAIL: " + message)

def read_json(path: Path):
    return json.loads(path.read_text())

inv = read_json(HERE / "inventory.json")
require(inv["target"]["repository_path"] == "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R374SingleCoordinateDegree.lean", "target path")
target = REPO / inv["target"]["repository_path"]
target_copy = HERE / inv["target"]["evidence_copy"]
require(sha(target) == inv["target"]["sha256"], "promoted target hash")
require(target.read_bytes() == target_copy.read_bytes(), "promoted target/source snapshot identity")

runner = HERE / inv["runner"]["path"]
require(sha(runner) == inv["runner"]["sha256"], "runner hash")

# Verify every archived proof-route source copy against its recorded exact hash.
for module, record in inv["proof_route_sources"].items():
    f = HERE / record["copy"]
    require(f.is_file() and sha(f) == record["sha256"], f"proof route source hash: {module}")
    require(record["pinned_host_source_matches"] is True and record["host_olean_present"] is True, f"pinned source/cache record: {module}")
# The direct local import is separately indexed for easy reviewer access.
for record in inv["direct_local_imports"]:
    f = HERE / record["evidence_copy"]
    require(sha(f) == record["sha256"], f"direct import source hash: {record['module']}")

# Route notes and the coordinate census are source evidence, not proof dependencies.
for key, hashkey in [("proof_route_note", "sha256")]:
    record = inv[key]
    require(sha(HERE / record["copy"]) == record[hashkey], "lead degree route hash")
    require(sha(HERE / record["prior_version_copy"]) == record["prior_version_sha256"], "preserved prior route hash")
    require(sha(HERE / record["selector_coordinate_census"]) == record["selector_census_sha256"], "selector census hash")
    require(sha(HERE / record["selector_census_manifest"]) == record["selector_census_manifest_sha256"], "selector census manifest hash")

# The pinned API inventory is nested and independently checksummed.
api = HERE / inv["api_cache_inventory"]
api_inv = read_json(api)
require(api_inv["local_recursive_aspis_module_count"] == 63 and api_inv["missing_local_modules"] == [], "API/cache closure inventory")
require(api_inv["all_host_sources_byte_match_local"] is True and api_inv["all_aspis_olean_present"] is True, "API/cache source and object presence")
require(api_inv["mathlib_commit"] == "9a04890da70b255c5e1b4da353fa697cf0dd3afe", "pinned Mathlib revision")
api_root = api.parent
for line in (api_root / "SHA256SUMS").read_text().splitlines():
    if not line.strip():
        continue
    expected, rel = line.split(None, 1)
    rel = rel.lstrip("* ")
    f = api_root / rel
    require(f.is_file() and sha(f) == expected, f"nested API/cache checksum: {rel}")
require(sha(api_root / "mathlib-source/Mathlib/Algebra/Polynomial/BigOperators.lean") == inv["direct_external_import"]["sha256"], "direct Mathlib source hash")

# Check each raw receipt against the copied source/log and the measurements in the index.
for run in inv["runs"]:
    source, log, receipt = (HERE / run[k] for k in ("source", "log", "receipt"))
    rec = read_json(receipt)
    require(sha(source) == run["source_sha256"] == rec["source_sha256"], f"source hash run {run['id']}")
    require(sha(log) == run["log_sha256"], f"log hash run {run['id']}")
    for k in ("exit_status", "wall_time", "peak_rss_kib", "swaps", "source_revision", "resources", "measurement_boundary", "complete_print_axioms"):
        require(run[k] == rec[k], f"receipt/index {k} mismatch run {run['id']}")
    txt = log.read_text(errors="replace")
    require(f"Elapsed (wall clock) time (h:mm:ss or m:ss): {run['wall_time']}" in txt, f"raw GNU time wall run {run['id']}")
    require(f"Maximum resident set size (kbytes): {run['peak_rss_kib']}" in txt, f"raw GNU time RSS run {run['id']}")
    require(f"Swaps: {run['swaps']}" in txt and f"Exit status: {run['exit_status']}" in txt, f"raw GNU time status/swap run {run['id']}")
    printed = re.findall(r"^'([^']+)' depends on axioms: \[(.*?)\]$", txt, re.M)
    require(len(printed) == len(run["complete_print_axioms"]), f"axiom report count run {run['id']}")
    require([f"'{name}' depends on axioms: [{axioms}]" for name, axioms in printed] == run["complete_print_axioms"], f"complete axiom text run {run['id']}")
    if run["exit_status"] == 0:
        for name, axioms in printed:
            require(set(x.strip() for x in axioms.split(",")) == FOUNDATIONS, f"non-foundational axiom in green run {run['id']} theorem {name}")
        require(len(printed) == inv["successful_axiom_report_count"], "successful axiom report count")
        require([x.rsplit(".", 1)[-1].split("'", 1)[0] for x, _ in printed] == inv["successful_axiom_report_names"], "successful theorem names")
    else:
        require("sorryAx" in txt, f"failed historical draft missing sorryAx report {run['id']}")
        require("Command exited with non-zero status 1" in txt, f"failed run not explicitly identified {run['id']}")

success = next(r for r in inv["runs"] if r["id"] == inv["successful_run_id"])
require(success["exit_status"] == 0 and success["swaps"] == 0, "green status/swap")
require(inv["boundary"] and inv["no_rebuild"] is True, "scope and no-rebuild record")
note = HERE.parents[1] / inv["publication_note"]
require(note.is_file() and sha(note) == inv["publication_note_sha256"], "publication note hash")

# The root checksum file is deliberately not self-listed.
checksum_file = HERE / "SHA256SUMS"
for line in checksum_file.read_text().splitlines():
    if not line.strip():
        continue
    expected, rel = line.split(None, 1)
    rel = rel.lstrip("* ")
    f = HERE / rel
    require(f.is_file() and sha(f) == expected, f"bundle checksum: {rel}")
listed = {line.split(None, 1)[1].lstrip("* ") for line in checksum_file.read_text().splitlines() if line.strip()}
actual = {str(f.relative_to(HERE)) for f in HERE.rglob("*") if f.is_file() and f != checksum_file}
require(listed == actual, "outer checksum file inventory mismatch")
print(f"PASS: R374 saved evidence ({len(actual)} files); target identity, 3 run receipts/logs, 8 green axiom reports, source route, selector census, and nested API/cache inventory verified offline")
