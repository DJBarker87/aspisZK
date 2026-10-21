#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text()); bad=[]
for row in m["files"]:
 p=root/row["path"]
 if not p.is_file(): bad.append("missing "+row["path"]); continue
 b=p.read_bytes()
 if hashlib.sha256(b).hexdigest()!=row["sha256"] or len(b)!=row["size_bytes"]: bad.append("checksum "+row["path"])
for p in root.rglob("*"):
 if p.is_file() and p.suffix in {".olean",".ilean"}: bad.append("binary "+str(p.relative_to(root)))
if bad: print("\n".join(bad)); sys.exit(1)
print(f"OK: {len(m['files'])} files; no Lean objects")
