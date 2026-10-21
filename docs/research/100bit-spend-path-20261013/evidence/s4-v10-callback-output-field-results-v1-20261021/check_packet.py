#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
receipt = json.loads((root/"receipts/callback-receipt.json").read_text())
cmd = json.loads((root/"receipts/callback-command.json").read_text())
pins = json.loads((root/"receipts/direct-import-pins.json").read_text())
assert receipt["exit_status"] == 0
assert receipt["source_sha256_before"] == receipt["source_sha256_after"]
assert receipt["source_sha256_after"] == sha(root/"sources/S4V10CallbackOutputFieldResultsV1.lean")
assert receipt["object_sha256"] and len(receipt["object_sha256"]) == 64
assert cmd["source_sha256_at_launch"] == receipt["source_sha256_after"]
assert cmd["launch_revision"] == receipt["launch_revision"]
log = (root/"receipts/callback-lean.log").read_text()
assert "concrete_candidate_dots_success_has_endpoint_fields" in log and "depends on axioms: [propext" in log
time = (root/"receipts/callback-time.log").read_text()
assert "maximum resident set size" in time and "swaps" in time
assert all(x["producer_object_sha256"] and len(x["producer_object_sha256"]) == 64 for x in pins["direct_imports"])
for x in pins["direct_imports"]:
    dep = root/"dependencies"/(x["module"]+".lean")
    assert sha(dep) == x["source_sha256"]
assert not list(root.rglob("*.olean")), "binary Lean artifacts are excluded"
for line in (root/"SHA256SUMS").read_text().splitlines():
    digest, rel = line.split("  ",1)
    assert sha(root/rel) == digest, rel
print("packet checks passed")
