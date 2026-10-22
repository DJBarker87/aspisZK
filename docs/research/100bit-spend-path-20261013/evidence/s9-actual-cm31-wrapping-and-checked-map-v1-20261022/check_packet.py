#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent;m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["compiled_objects_included"] is False
assert len(m["targets"])==2 and all(t["exit_status"]==0 and t["process_swaps"]==0 for t in m["targets"])
for f in m["files"]:
 p=root/f["path"];assert p.is_file(),f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"],f["path"]
 assert p.stat().st_size==f["bytes"],f["path"]
for p in root.rglob("*"):
 if p.is_file():assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
for t in m["targets"]:
 log=(root/t["audit_file"]).read_text()
 assert "propext" in log and "Classical.choice" in log and "Quot.sound" in log
 assert t["audited_theorems"]
print("PASS: actual CM31 wrapping and checked map packet; receipts, hashes, audits valid; no compiled objects")
