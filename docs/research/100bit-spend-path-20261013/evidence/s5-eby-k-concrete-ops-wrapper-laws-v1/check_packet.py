#!/usr/bin/env python3
import hashlib,json,pathlib,sys
p=pathlib.Path(__file__).resolve().parent
m=json.loads((p/"manifest.json").read_text())
for rel,h in [(m["target_source"],m["target_source_sha256"])]:
 a=hashlib.sha256((p/rel).read_bytes()).hexdigest()
 assert a==h,(rel,a,h)
r=json.loads((p/"evidence/receipt.json").read_text())
assert r["exit_status"]==0 and r["source_sha256"]==m["target_source_sha256"]
assert r["argv"][-1].endswith("EbyKConcreteOpsWrapperLawsV1.lean")
log=(p/"evidence/lean.log").read_text()
for n in m["theorems"]:
 assert f"AspisR1S5EbyKConcreteOpsWrapperLawsV1.{n}" in log
assert "sorryAx" not in log
assert set(x for x in m["axioms"] if x not in log)==set(), "axiom audit not represented in log"
for f in p.rglob("*"):
 if f.is_file():
  assert f.suffix not in {".olean",".ilean",".ir",".llbc"},f
print("PASS")
