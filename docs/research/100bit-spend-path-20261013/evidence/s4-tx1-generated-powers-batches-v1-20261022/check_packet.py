#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((ROOT / "manifest.json").read_text())
pre = json.loads((ROOT / manifest["preflight"]).read_text())
receipt = json.loads((ROOT / manifest["launch_receipt"]).read_text())
command = json.loads((ROOT / manifest["launch_command"]).read_text())
source = ROOT / manifest["source"]
log = (ROOT / manifest["lean_raw_log"]).read_text()
profile = (ROOT / manifest["profile"]).read_text().strip()

assert manifest["schema"] == "focused-extractor-proof-packet-v1"
assert manifest["object_included"] is False and manifest["compiled_objects_included"] is False
assert sha(source) == manifest["source_sha256"] == receipt["source_sha256"]
assert receipt["source_revision_at_launch"] == manifest["source_revision_at_launch"]
assert receipt["exit_status"] == manifest["launch_metrics"]["exit_status"] == 0
assert receipt["object_sha256"] == manifest["external_object_sha256"]
assert receipt["wall_seconds"] == manifest["launch_metrics"]["wall_seconds"]
assert receipt["peak_aggregate_rss_bytes"] == manifest["launch_metrics"]["peak_aggregate_rss_bytes"]
assert receipt["peak_process_rss_bytes"] == manifest["launch_metrics"]["peak_process_rss_bytes"]
assert receipt["process_swaps"] == manifest["launch_metrics"]["process_swaps"] == 0
reports = re.findall(r"'" + re.escape(manifest["theorem"]) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
assert len(reports) == 1
assert set(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", reports[0])) == set(manifest["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
assert "sorryAx" not in log and not re.search(r"(?m)^.*: error:", log)
assert sha(ROOT / manifest["profile"]) == pre["profile_sha256"] if "profile_sha256" in pre else True
assert profile in next(x for x in command["argv"] if x.startswith("LEAN_PATH="))
assert pre["source_sha256"] == manifest["source_sha256"]
assert pre["source_revision"] == manifest["source_revision_at_launch"]
assert pre["direct_imports"] == json.loads((ROOT / manifest["direct_import_pins"]).read_text())
assert set(pre["direct_imports"]) == {"S4Tx1WholeExactBatchesRootV1", "S4InstalledPrepareRawEarlyPowersV1"}
for row in json.loads((ROOT / manifest["source_pins"]).read_text()):
    assert sha(ROOT / row["packet_source"]) == row["source_sha256"]
assert {row["module"] for row in json.loads((ROOT / manifest["source_pins"]).read_text())} == {
    "S4Tx1WholeExactBatchesRootV1", "S4InstalledPrepareRawEarlyPowersV1", "S4InstalledEarlyPowersEquationV1"
}
assert not list(ROOT.rglob("*.olean")) and not list(ROOT.rglob("*.pyc"))
for line in (ROOT / "SHA256SUMS").read_text().splitlines():
    digest, rel = line.split("  ", 1)
    assert sha(ROOT / rel) == digest, rel
print("PASS: source-only whole-caller powers/batches packet")
