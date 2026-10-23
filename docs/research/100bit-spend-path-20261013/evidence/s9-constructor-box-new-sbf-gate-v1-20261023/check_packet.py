#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-sbf-stack-gate-packet-v1"
assert m["status"]=="build-succeeded-stack-gate-failed" and m["stack_gate_pass"] is False
assert m["candidate_stack_diagnostic"]["excess_bytes"]==504
assert m["scope_limits_bytes"]=={"memory_high":3221225472,"memory_max":4294967296,"memory_swap_max":0}
for row in m["files"]:
 p=root/row["path"]
 assert p.is_file(),row["path"]
 data=p.read_bytes()
 assert len(data)==row["bytes"],row["path"]
 assert hashlib.sha256(data).hexdigest()==row["sha256"],row["path"]
 assert p.suffix not in {".so",".o",".olean",".llbc"},row["path"]
assert hashlib.sha256((root/"source/weights.base.rs").read_bytes()).hexdigest()==m["base_weights_sha256"]
assert hashlib.sha256((root/"source/weights.candidate.rs").read_bytes()).hexdigest()==m["candidate_weights_sha256"]
log=(root/"build/build.log").read_text()
assert "Stack offset of 4600 exceeded max offset of 4096 by 504 bytes" in log
assert "Finished `release` profile" in log
assert not any(p.suffix==".so" for p in root.rglob("*"))
print("PASS: SBF gate evidence hashes; candidate stack gate correctly classified FAIL")
