#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parent
errors=[]
for line in (R/"SHA256SUMS").read_text().splitlines():
 h,rel=line.split("  ",1);p=R/rel
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=h:errors.append("sha:"+rel)
for p in R.rglob("*"):
 if p.is_file() and (p.suffix.lower() in {".olean",".ilean",".so",".a",".o",".elf",".bin",".rlib"} or ".olean." in p.name):errors.append("binary:"+str(p.relative_to(R)))
C=json.loads((R/"remote/attempt23/config.json").read_text())
if len(C["stages"])!=20:errors.append("stage-count")
for st in C["stages"][1:]:
 ev=R/"remote/attempt23/attempt"/(st["phase"]+"-evidence")
 q=json.loads((ev/"receipt.json").read_text())
 if q.get("exit_status")!=0 or q.get("source_sha256")!=st["source_sha256"] or q.get("scope_swap_peak_bytes")!=0:errors.append("receipt:"+st["phase"])
 src=R/"remote/attempt23/sources"/Path(st["source"]).relative_to("sources")
 if not src.is_file() or hashlib.sha256(src.read_bytes()).hexdigest()!=st["source_sha256"]:errors.append("source:"+st["phase"])
closure=json.loads((R/"remote/attempt23/union-import-closure.json").read_text())
if len(closure.get("owners",{}))!=5119 or closure.get("missing"):errors.append("closure")
if errors:print("FAIL\n"+"\n".join(errors));sys.exit(1)
print("PASS: 20 stages (19 rebuilt, stage01 reused); all receipts/source hashes match; 5,119 import owners; no binaries")
