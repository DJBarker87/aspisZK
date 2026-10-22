#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m.get("schema")=="focused-extractor-proof-packet-v1"
for f in m["files"]:
 p=root/f["path"]; assert p.is_file(), f"missing {p}"; assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"], f"hash mismatch {p}"; assert p.stat().st_size==f["size_bytes"]
for mod in m["modules"]:
 assert mod["exit_status"]==0
 assert mod["swap_bytes"]==0
 assert mod["source_sha256"]
 assert set(mod["axioms"]).issubset({"propext","Classical.choice","Quot.sound"})
print(f"OK {m['packet']}: {len(m['modules'])} modules, {len(m['files'])} files")
