#!/usr/bin/env python3
"""Read-only portable consistency check for saved R353 compile evidence."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = Path(__file__).resolve().parents[5]

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = json.loads((HERE / "manifest.json").read_text())
receipt = json.loads((HERE / "compile-receipt.json").read_text())
provenance = json.loads((HERE / "release-provenance.json").read_text())
source = HERE / "source/R353AfterGuardsCriterion.lean"
snapshot = HERE / "source/R353AfterGuardsCriterion.compile-snapshot.lean"
assert sha(source) == sha(snapshot) == receipt["source_sha256"] == manifest["source_sha256"]
assert sha(snapshot) == provenance["compile_source_snapshot_sha256"]
imports = {
    "AspisV8R19.R350AfterGuardsExecution": HERE / "imports/AspisV8R19_R350AfterGuardsExecution.lean",
    "AspisV8R19.R341PrefixNonzero": HERE / "imports/AspisV8R19_R341PrefixNonzero.lean",
}
actual = re.findall(r"^import\s+([A-Za-z0-9_.]+)", source.read_text(), re.M)
assert set(actual) == set(imports) == set(receipt["direct_local_import_sha256"])
for name, path in imports.items():
    assert sha(path) == receipt["direct_local_import_sha256"][name]
    assert sha(path) == provenance["direct_local_imports"][name]["sha256"]

axioms = (HERE / "axioms.txt").read_text().strip()
log = (HERE / "logs/aspis-focus-1790940987638478000.log").read_text()
assert axioms in log and "sorryAx" not in axioms
assert manifest["complete_print_axioms"] == receipt["complete_print_axioms"]
assert len(manifest["complete_print_axioms"]) == 3
assert manifest["exit_status"] == receipt["exit_status"] == 0
assert manifest["wall_time"] == receipt["wall_time"] == "0:01.55"
assert manifest["peak_rss_kib"] == receipt["peak_rss_kib"] == 3712312
assert manifest["swaps"] == receipt["swaps"] == 0
for key in ("MemoryHigh", "MemoryMax", "MemorySwapMax", "TasksMax"):
    assert manifest["resources"][key] == receipt["resources"][key]
assert manifest["resources"]["flags"] == receipt["resources"]["lean_flags"]

failed = HERE / "history/1790940942142204000"
r = json.loads((failed / "receipt.json").read_text())
assert sha(failed / "source.lean") == r["source_sha256"]
assert r["exit_status"] == 1 and "sorryAx" in " ".join(r["complete_print_axioms"])
assert "Exit status: 1" in (failed / "compile.log").read_text()
assert "sorryAx" not in (HERE / "axioms.txt").read_text()

head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip()
rev = receipt["source_revision"]
assert rev == provenance["compile_campaign_revision"]
assert subprocess.run(["git", "merge-base", "--is-ancestor", rev, head], cwd=REPO).returncode == 0
assert provenance["current_HEAD_equality_required"] is False

graph = json.loads((HERE / "local-import-graph.json").read_text())
assert graph["acyclic"] and graph["cycle_count"] == 0
index = json.loads((HERE / "SHA256SUMS.json").read_text())
for rel, expected in index.items():
    path = HERE / rel
    assert path.is_file() and sha(path) == expected, rel
print(json.dumps({"overall": "PASS", "compile_revision": rev, "audit_head": head,
                  "source_sha256": sha(source), "direct_imports": len(imports),
                  "graph_nodes": graph["node_count"], "graph_edges": graph["edge_count"],
                  "rejected_history_id": "1790940942142204000", "axiom_reports": len(manifest["complete_print_axioms"])}))
