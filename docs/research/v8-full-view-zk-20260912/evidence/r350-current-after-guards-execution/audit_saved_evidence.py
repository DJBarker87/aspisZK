#!/usr/bin/env python3
"""Read-only portable consistency check for the saved R350 evidence bundle."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = Path(__file__).resolve().parents[5]

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = json.loads((HERE / "manifest.json").read_text())
receipt = json.loads((HERE / "compile-receipt.json").read_text())
provenance = json.loads((HERE / "release-provenance.json").read_text())
source = HERE / "source/R350AfterGuardsExecution.lean"
snapshot = HERE / "source/R350AfterGuardsExecution.compile-snapshot.lean"
assert sha(source) == manifest["source_sha256"] == receipt["source_sha256"]
assert source.read_bytes() == snapshot.read_bytes()
assert sha(snapshot) == provenance["compile_source_snapshot_sha256"]

imports = {
    "AspisR346AfterGuardsRaw": HERE / "imports/AspisR346AfterGuardsRaw.lean",
    "AspisV8R19.R336PrefixPairInverseExecution": HERE / "imports/AspisV8R19_R336PrefixPairInverseExecution.lean",
    "AspisV8R19.R342OutputSetup": HERE / "imports/AspisV8R19_R342OutputSetup.lean",
}
source_imports = re.findall(r"^import\s+([A-Za-z0-9_.]+)", source.read_text(), re.M)
assert set(source_imports) == set(imports)
assert set(source_imports) == set(receipt["direct_local_import_sha256"])
for name, path in imports.items():
    assert sha(path) == receipt["direct_local_import_sha256"][name]
    assert sha(path) == provenance["direct_local_imports"][name]["sha256"]

axiom_text = (HERE / "axioms.txt").read_text()
log_text = (HERE / "logs/aspis-focus-1790940499136105000.log").read_text()
assert axiom_text.strip() in log_text
assert len(manifest["complete_print_axioms"]) == 3
assert all("sorryAx" not in item and "native_decide" not in item for item in manifest["complete_print_axioms"])
assert "sorryAx" not in axiom_text
assert manifest["exit_status"] == receipt["exit_status"] == 0
assert manifest["wall_time"] == receipt["wall_time"] == "0:01.59"
assert manifest["peak_rss_kib"] == receipt["peak_rss_kib"] == 3716348
assert manifest["swaps"] == receipt["swaps"] == 0
assert manifest["resources"]["MemoryHigh"] == receipt["resources"]["MemoryHigh"]
assert manifest["resources"]["MemoryMax"] == receipt["resources"]["MemoryMax"]
assert manifest["resources"]["MemorySwapMax"] == receipt["resources"]["MemorySwapMax"]
assert manifest["resources"]["TasksMax"] == receipt["resources"]["TasksMax"]
assert manifest["resources"]["flags"] == receipt["resources"]["lean_flags"]

history = json.loads((HERE / "history-index.json").read_text())
for run in history["runs"]:
    folder = HERE / "history" / run["run_id"]
    r = json.loads((folder / "receipt.json").read_text())
    assert sha(folder / "source.lean") == r["source_sha256"] == run["source_sha256"]
    assert f'Exit status: {r["exit_status"]}' in (folder / "compile.log").read_text()
    has_sorry = any("sorryAx" in item for item in r["complete_print_axioms"])
    assert has_sorry == run["sorryAx_in_failed_or_intermediate_report"]
    if run["exit_status"] != 0:
        assert run["classification"].startswith("rejected")
        if has_sorry:
            assert "failed-history" in run["classification"] or "rejected" in run["classification"]

# The compile revision is checked as an ancestor, not required to equal current HEAD.
head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip()
rev = receipt["source_revision"]
assert rev == provenance["compile_campaign_revision"]
assert subprocess.run(["git", "merge-base", "--is-ancestor", rev, head], cwd=REPO).returncode == 0
assert provenance["current_HEAD_equality_required"] is False

graph = json.loads((HERE / "local-import-graph.json").read_text())
assert graph["acyclic"] is True and graph["cycle_count"] == 0
assert graph["node_count"] == 77 and graph["edge_count"] == 113

# Validate the portable bundle index (which excludes itself) and all listed payloads.
index = json.loads((HERE / "SHA256SUMS.json").read_text())
for rel, expected in index.items():
    path = HERE / rel
    assert path.is_file() and sha(path) == expected, rel
print(json.dumps({"overall": "PASS", "compile_revision": rev, "audit_head": head,
                  "source_sha256": sha(source), "direct_imports": len(imports),
                  "import_graph_nodes": graph["node_count"], "import_graph_edges": graph["edge_count"],
                  "history_runs": len(history["runs"]), "axiom_reports": len(manifest["complete_print_axioms"])}))
