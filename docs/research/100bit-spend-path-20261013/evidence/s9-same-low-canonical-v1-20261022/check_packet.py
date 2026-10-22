#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re

root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m = json.loads((root / "manifest.json").read_text())
src = root / m["source"]
profile = root / m["profile"]
receipt = json.loads((root / m["launch_receipt"]).read_text())
preflight = json.loads((root / m["preflight"]).read_text())
closure = json.loads((root / m["closure_preflight"]).read_text())
assert sha(src) == m["source_sha256"] == receipt["source_sha256"]
assert "theorem active_body_scalar_low_canonical" in src.read_text()
assert sha(profile) == m["profile_sha256"] == preflight["profile_sha256"]
assert receipt["exit_status"] == 0 and receipt["object_sha256"] == m["external_object_sha256"]
assert closure["missing"] == [] and closure["modules"] == m["closure"]["modules"]
log = (root / m["lean_raw_log"]).read_text()
decl, axioms = next(iter(m["theorems"].items()))
match = re.search(re.escape("'" + decl + "' depends on axioms:") + r"([^\n]*(?:\n\s+[^\n]*){0,3})", log)
assert match, f"missing named axiom report for {decl}"
assert all(a in match.group(1) for a in axioms), match.group(1)
assert "sorryAx" not in match.group(1), match.group(1)
assert not list(root.rglob("*.olean")), "packet must remain source-only"
print("PASS source-only packet; theorem declaration, import closure, receipt, and named axioms verified")
