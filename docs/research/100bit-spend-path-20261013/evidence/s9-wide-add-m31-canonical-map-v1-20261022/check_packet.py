#!/usr/bin/env python3
import hashlib,json,pathlib
r=pathlib.Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and not m["compiled_objects_included"]
for f in m["files"]:
 p=r/f["path"];assert p.is_file(),f"missing {p}";assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"],f"hash mismatch {p}";assert p.suffix not in {".olean",".ilean",".pyc"},f"forbidden {p}"
assert not list(r.rglob("*.olean")) and not list(r.rglob("*.ilean")) and not list(r.rglob("*.pyc"))
for k,v in m["source_owners"].items(): assert v["source_sha256"] and v["object_sha256"]
print("PASS",m["packet"],len(m["files"]),"source/evidence files")
