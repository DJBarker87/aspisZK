#!/usr/bin/env python3
"""Validate the source-only S5 P6 row-28 joint-trace packet."""
import hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def fail(s): print("FAIL: "+s,file=sys.stderr); raise SystemExit(1)
m=json.loads((ROOT/"manifest.json").read_text())
if m.get("schema")!="focused-extractor-proof-packet-v1": fail("schema")
listed={x["path"]:x for x in m.get("files",[])}
actual={x.relative_to(ROOT).as_posix() for x in ROOT.rglob("*") if x.is_file() and x.name not in {"manifest.json","SHA256SUMS"}}
if actual!=set(listed): fail(f"file inventory mismatch: extra={actual-set(listed)}, absent={set(listed)-actual}")
for rel,x in listed.items():
 p=ROOT/rel
 if sha(p)!=x["sha256"] or p.stat().st_size!=x["size_bytes"]: fail("pin mismatch "+rel)
 if p.suffix in {".olean",".ilean",".ir",".llbc"}: fail("binary "+rel)
for mod in m["modules"]:
 s=ROOT/mod["source"]
 if sha(s)!=mod["source_sha256"]: fail("module source "+mod["module"])
 c=json.loads((ROOT/mod["command"]).read_text()); r=json.loads((ROOT/mod["receipt"]).read_text())
 if c.get("source_sha256")!=mod["source_sha256"] or r.get("source_sha256")!=mod["source_sha256"]: fail("launch source pin "+mod["module"])
 if c.get("git_head_at_launch")!=m.get("source_revision","").split()[-1]: fail("launch revision "+mod["module"])
 if r.get("exit_status")!=0 or r.get("object_sha256")!=mod["object_sha256"] or r.get("swaps")!=0: fail("receipt "+mod["module"])
 a=c.get("argv",[])
 if "-j1" not in a or "-M" not in a or "4400" not in a: fail("resource flags "+mod["module"])
 log=(ROOT/mod["log"]).read_text()
 if "sorryAx" in log or "depends on axioms:" not in log: fail("axiom audit "+mod["module"])
 for ax in mod["axioms"]:
  if ax not in log: fail("axiom missing "+ax)
for name,dep in m["direct_import_source_map"].items():
 if sha(ROOT/dep["source"])!=dep["source_sha256"]: fail("dependency source "+name)
 producer=ROOT.parents[1]/dep["producer_packet"]
 if not producer.is_file(): fail("producer packet missing "+name)
for line in (ROOT/"SHA256SUMS").read_text().splitlines():
 h,rel=line.split("  ",1)
 if sha(ROOT/rel)!=h: fail("checksum "+rel)
print(f"PASS: {len(listed)} files, {len(m['modules'])} accepted module, no binaries")
