#!/usr/bin/env python3
"""Recheck saved R346 publication evidence without modifying archived evidence."""
from pathlib import Path
import hashlib
import json
import subprocess

EV = Path(__file__).resolve().parent
WT = EV.parents[4]
SCRATCH_REPORT = WT / ".r21-scratch/r346-publication-audit/reusable-check.json"
BUNDLE = EV / "staging-bundle"
sha = lambda data: hashlib.sha256(data).hexdigest()

def digest(path):
    return sha(Path(path).read_bytes())

def assert_manifest(root, filename):
    for line in (root / filename).read_text().splitlines():
        expected, relative = line.split("  ", 1)
        assert digest(root / relative) == expected, f"{filename}: {relative}"

receipt = json.loads((EV / "aspis-focus-1790938589371152000.receipt.json").read_text())
staging_audit = json.loads((BUNDLE / "raw-binding-audit.json").read_text())
compile_time_audit = json.loads((EV / "saved-evidence-audit.json").read_text())
formatting = json.loads((EV / "formatting-preservation.json").read_text())
source_snapshot = EV / "AspisR346AfterGuardsRaw.compile-snapshot.lean"
promoted_source = EV / "source/AspisR346AfterGuardsRaw.lean"
current_target = WT / "docs/research/v8-full-view-zk-20260912/lean/AspisR346AfterGuardsRaw.lean"
assert digest(source_snapshot) == digest(promoted_source) == digest(current_target) == receipt["source_sha256"]
assert digest(source_snapshot) == "8035e6ba3d723e709c8897e65bc8517a849207857f03fe6979612f8e0d5b83e8"
assert receipt["source_revision"] == compile_time_audit["compile_revision"]
current_revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=WT, text=True).strip()
subprocess.run(["git", "merge-base", "--is-ancestor", receipt["source_revision"], "HEAD"], cwd=WT, check=True)

# Re-extract only from archived frozen inputs and compare the selected exact bytes.
funs = (BUNDLE / "provenance/R292Funs.input.lean").read_text()
start = "        let i1 := Slice.len xs\n"
end = "        ok (core.result.Result.Ok (ox2, oy2))\n"
i = funs.index(start)
j = funs.index(end, i) + len(end)
fragment = funs[i:j]
assert sha(fragment.encode()) == staging_audit["fragment_sha256"] == compile_time_audit["source_fragment_sha256"]
assert (BUNDLE / "selected-source-fragment.txt").read_text().endswith(fragment)
types = (BUNDLE / "provenance/R292Types.input.lean").read_text()
e0 = types.index("/-- [aspis_v8_performance_host::Error]")
e1 = types.index("/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::closure]", e0)
error_copy = types[e0:e1]
assert sha(error_copy.encode()) == staging_audit["error_declaration_sha256"] == compile_time_audit["error_copy_sha256"]
lean = (BUNDLE / "AspisR346AfterGuardsRaw.lean").read_text()
assert error_copy in lean
assert "import AspisR316SliceLastRaw" in lean and "open AspisR316SliceLastRaw" in lean
assert "import AspisR156FullFreeze.Types" not in lean
assert "AspisR346AfterGuardsRaw.Error" in lean

# Verify pinned local dependency bytes and the copied R316 raw binding.
local_imports = receipt["direct_local_import_sha256"]
module_files = {
    "AspisR318BatchPrefixRaw": "AspisR318BatchPrefixRaw.lean",
    "AspisR305BatchReverseRaw": "AspisR305BatchReverseRaw.lean",
    "AspisR278PrivateInverseRaw": "AspisR278PrivateInverseRaw.lean",
    "AspisR340BatchOutputRaw": "AspisR340BatchOutputRaw.lean",
    "AspisR316SliceLastRaw": "AspisR316SliceLastRaw.lean",
}
for module, filename in module_files.items():
    assert digest(WT / "docs/research/v8-full-view-zk-20260912/lean" / filename) == local_imports[module]
assert digest(BUNDLE / "provenance/AspisR316SliceLastRaw.lean") == local_imports["AspisR316SliceLastRaw"]

log = EV / "logs/aspis-focus-1790938589371152000.log"
log_bytes = log.read_bytes()
assert sha(log_bytes) == formatting["compile_log_sha256"]
assert b"\r\nWarning: Permanently added" in log_bytes
assert b"Exit status: 0" in log_bytes and b"Swaps: 0" in log_bytes
axioms = (EV / "axioms.txt").read_text()
assert all(line in axioms for line in receipt["complete_print_axioms"])
assert "sorryAx" not in axioms and "native_decide" not in axioms
assert receipt["exit_status"] == compile_time_audit["exit_status"] == 0
assert receipt["wall_time"] == compile_time_audit["wall_time"]
assert receipt["peak_rss_kib"] == compile_time_audit["peak_rss_kib"]
assert receipt["swaps"] == compile_time_audit["swaps"] == 0

# Bundle and outer inventories must be valid; manifests omit themselves to avoid cycles.
assert_manifest(BUNDLE, "SHA256SUMS")
outer = json.loads((EV / "SHA256SUMS.json").read_text())
for relative, expected in outer.items():
    assert digest(EV / relative) == expected, f"outer inventory: {relative}"
assert set(outer) == set((EV / "FILES.txt").read_text().splitlines())

report = {
    "status": "saved evidence recheck passed; no Lean execution; no archived files modified",
    "target_sha256": digest(current_target),
    "source_revision": receipt["source_revision"],
    "current_revision": current_revision,
    "compile_revision_is_ancestor": True,
    "source_fragment_sha256": sha(fragment.encode()),
    "error_copy_sha256": sha(error_copy.encode()),
    "R316_binding_sha256": local_imports["AspisR316SliceLastRaw"],
    "direct_local_imports_verified": sorted(local_imports),
    "exit_status": receipt["exit_status"],
    "wall_time": receipt["wall_time"],
    "peak_rss_kib": receipt["peak_rss_kib"],
    "swaps": receipt["swaps"],
    "resource_limits": receipt["resources"],
    "complete_axioms": receipt["complete_print_axioms"],
    "outer_inventory_entries_verified": len(outer),
    "scope": "Raw source compilation evidence only; no execution correspondence, guard proof, or source-library semantic conclusion."
}
SCRATCH_REPORT.parent.mkdir(parents=True, exist_ok=True)
SCRATCH_REPORT.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
