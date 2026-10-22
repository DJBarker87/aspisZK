#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
def sh(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errs=[]
for x in m["files"]:
 p=r/x["path"]
 if not p.is_file() or sh(p)!=x["sha256"] or p.stat().st_size!=x["size_bytes"]:errs.append("file:"+x["path"])
mod=m["modules"][0];rec=json.loads((r/mod["receipt"]).read_text())
if rec.get("exit_status")!=0 or rec.get("source_sha256")!=mod["source_sha256"] or rec.get("object_sha256")!=mod["object_sha256"]:errs.append("receipt mismatch")
if sh(r/mod["source"])!=mod["source_sha256"]:errs.append("main source mismatch")
for n,d in m["direct_import_source_map"].items():
 if sh(r/d["source"])!=d["source_sha256"]:errs.append("dependency source:"+n)
for n,d in m.get("selected_transitive_source_owners",{}).items():
 if sh(r/d["source"])!=d["source_sha256"]:errs.append("selected owner source:"+n)
if any(p.suffix==".olean" for p in r.rglob("*")):errs.append("binary included")
if errs:print("FAIL\n"+"\n".join(errs));sys.exit(1)
print("PASS",len(m["files"]),"files",len(m["direct_import_source_map"]),"direct imports")
