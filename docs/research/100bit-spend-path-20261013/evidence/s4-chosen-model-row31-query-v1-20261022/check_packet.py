#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((r/"manifest.json").read_text()); rec=json.loads((r/"receipt/receipt.json").read_text())
s=r/"sources/ChosenModelRow31QueryV1.lean"
assert sha(s)==m["source_sha256"]==rec["source_sha256"]
assert rec["exit_status"]==0 and rec["process_swaps"]==0 and rec["watchdog_abort"] is None
assert rec["object_sha256"]==m["object_sha256"]
assert sha(r/"receipt/LEAN_PATH.txt")==m["closure"]["profile_sha256"]
assert m["closure"]["module_count"]==6063 and m["closure"]["missing"]==[]
assert m["axioms"]==["propext","Classical.choice","Quot.sound"]
for pin in m["direct_imports"]:
 p=Path(pin["object_path"]); assert p.exists() and sha(p)==pin["object_sha256"]
 if pin["source_path"]:
  q=Path(pin["source_path"]); assert q.exists() and sha(q)==pin["source_sha256"]
assert not list(r.rglob("*.olean")) and not list(r.rglob("*.llbc"))
log=(r/"receipt/lean.log").read_text()
assert "error:" not in log and "sorryAx" not in log
full=m["namespace"]+"."+m["theorem"]
reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log)
assert len(reports)==1 and reports[0][0]==full
assert set(re.findall(r"[A-Za-z_][A-Za-z_0-9.]*",reports[0][1])) <= {"propext","Classical.choice","Quot.sound"}
assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b",s.read_text())
for line in (r/"SHA256SUMS").read_text().splitlines():
 digest,name=line.split(None,1); assert sha(r/name.lstrip(" *"))==digest,name
assert not any(p.suffix in {".olean",".ilean",".ir",".o",".llbc"} for p in r.rglob("*") if p.is_file())
print("PASS: chosen-model coordinates, named compiler axiom report, import pins and packet inventory")
