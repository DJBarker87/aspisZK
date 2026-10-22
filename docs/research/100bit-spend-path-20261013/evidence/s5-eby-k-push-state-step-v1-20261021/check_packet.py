#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parent
m=json.loads((r/"manifest.json").read_text())
def sh(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errs=[]
for x in m["files"]:
 p=r/x["path"]
 if not p.is_file() or sh(p)!=x["sha256"] or p.stat().st_size!=x["size_bytes"]: errs.append(x["path"])
rec=json.loads((r/"evidence/receipt.json").read_text())
mod=m["modules"][0]
if rec.get("exit_status")!=0 or rec.get("source_sha256")!=mod["source_sha256"] or rec.get("object_sha256")!=mod["object_sha256"]: errs.append("receipt/module mismatch")
if sh(r/mod["source"])!=mod["source_sha256"]: errs.append("selected source mismatch")
for n,d in m["direct_import_source_map"].items():
 if sh(r/d["repository_path"])!=d["source_sha256"]: errs.append("dependency source mismatch: "+n)
 if d["object_sha256"] not in json.dumps(d): errs.append("dependency object pin missing: "+n)
if any(p.suffix==".olean" for p in r.rglob("*")): errs.append("compiled binary included")
if errs: print("FAIL",*errs,sep="\n"); sys.exit(1)
print("PASS",len(m["files"]),"frozen files",len(m["direct_import_source_map"]),"direct imports")
