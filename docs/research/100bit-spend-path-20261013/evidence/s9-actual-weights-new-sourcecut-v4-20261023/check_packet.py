#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent
m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
assert m["scope"]["compiled_objects_included"] is False and m["scope"]["raw_llbc_included"] is False
for f in m["files"]:
 p=r/f["path"]; b=p.read_bytes()
 assert len(b)==f["bytes"] and hashlib.sha256(b).hexdigest()==f["sha256"],f["path"]
for owner in m["owner_compiles"]:
 assert owner["exit_status"]==0 and owner["process_swaps"]==0
 part=owner["module"].split("/")[-1].lower(); log=(r/"proof"/part/"lean.log").read_text()
 assert "error:" not in log and "sorryAx" not in log
for p in r.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
print("PASS: constructor sourcecut provenance packet")
