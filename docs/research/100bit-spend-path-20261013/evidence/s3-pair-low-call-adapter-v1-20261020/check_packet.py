#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
errors=[]
for t in m["targets"]:
    sp=root/t["source"]
    if not sp.is_file(): errors.append(f"missing source {sp}"); continue
    h=hashlib.sha256(sp.read_bytes()).hexdigest()
    if h != t["source_sha256"]: errors.append(f"source hash mismatch {t['module']}: {h}")
    if t.get("compile_log"):
        lp=root/t["compile_log"]
        if not lp.is_file(): errors.append(f"missing compile log {lp}")
        elif t.get("compile_log_sha256") and hashlib.sha256(lp.read_bytes()).hexdigest() != t["compile_log_sha256"]: errors.append(f"compile log hash mismatch {t['module']}")
for d in m.get("diagnostics", []):
    for key in ("source", "compile_log"):
        rel=d.get(key)
        if not rel: continue
        fp=root/rel
        if not fp.is_file(): errors.append(f"missing diagnostic {fp}")
        elif d.get(key+"_sha256") and hashlib.sha256(fp.read_bytes()).hexdigest() != d[key+"_sha256"]: errors.append(f"diagnostic hash mismatch {rel}")
for rel in ["README.md","manifest.json"]:
    if not (root/rel).is_file(): errors.append(f"missing {rel}")
if errors:
    print("\n".join(errors)); sys.exit(1)
print(f"PASS: {len(m['targets'])} selected source snapshots; object hashes are external cache pins (no binaries included)")
