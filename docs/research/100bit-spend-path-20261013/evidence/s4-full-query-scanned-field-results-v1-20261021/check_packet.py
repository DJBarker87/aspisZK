#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root=pathlib.Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
assert m["exit_status"]==0
s=root/"sources/S4FullQueryValuesPrefixV1.lean"
assert sha(s)==m["source_sha256"]
assert sha(s)==m["original_compiled_source_sha256"]
assert sha(m["object_path"])==m["object_sha256"]
for owner,pin in m["direct_import_source_map"].items():
    assert sha(pin["selected_object_path"])==pin["object_sha256"], owner
    assert sha(pin["source_path"])==pin["source_sha256"], owner
assert "full_query_values_success_scanned_field_results" in s.read_text()
assert "[propext,\n Classical.choice,\n Quot.sound]" in (root/"receipts/lean.log").read_text()
for p in root.rglob("*.olean"): raise AssertionError(f"binary included: {p}")
print("packet pins and proof receipt verified")
