from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["compiled_objects_included"] is False
for f in m["files"]:
 p=root/f["path"]; assert p.is_file(), f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"], f["path"]
assert not list(root.rglob("*.olean")) and not list(root.rglob("*.ilean"))
r=json.loads((root/"run/receipt.json").read_text())
assert r["exit_status"]==0 and r["process_swaps"]==0
src=root/"sources/S9WideFullCurrentSuffixV1.lean"
assert r["source_sha256"]==hashlib.sha256(src.read_bytes()).hexdigest()==m["source_sha256"]
assert r["object_sha256"]==m["object_sha256"]
log=(root/"run/lean.log").read_text()
assert "qcut_tail_after_q3_maps_to_current" in log and "sorryAx" not in log
f=json.loads((root/"diagnostics/prior-mapper-head-memory-failure/receipt.json").read_text())
assert f["exit_status"] != 0 and f["process_swaps"] == 0
assert f["source_sha256"] == m["prior_failed_attempt"]["source_sha256"]
print("PASS")
