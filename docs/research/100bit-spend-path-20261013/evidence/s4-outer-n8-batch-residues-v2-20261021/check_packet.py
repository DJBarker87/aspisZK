#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text());bad=[]
for x in m["files"]:
 p=r/x["path"]
 if not p.is_file():bad.append("missing "+x["path"]);continue
 b=p.read_bytes()
 if hashlib.sha256(b).hexdigest()!=x["sha256"] or len(b)!=x["size_bytes"]:bad.append("checksum "+x["path"])
for p in r.rglob("*"):
 if p.is_file() and p.suffix in {".olean",".ilean"}:bad.append("binary "+str(p.relative_to(r)))
if bad:print("\n".join(bad));sys.exit(1)
print(f"OK: {len(m['files'])} files; no Lean objects")
