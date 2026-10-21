#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent
m = json.loads((root / "manifest.json").read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
for row in m["files"]:
    p=root/row["path"]
    if not p.is_file(): errors.append(f"missing file: {row['path']}"); continue
    if sha(p)!=row["sha256"]: errors.append(f"hash mismatch: {row['path']}")
    if p.stat().st_size != row["size_bytes"]: errors.append(f"size mismatch: {row['path']}")
for row in m["modules"]:
    receipt=json.loads((root/row["receipt"]).read_text())
    source=root/row["source"]
    if sha(source)!=row["source_sha256"]: errors.append("module source hash mismatch")
    if receipt.get("exit_status")!=0: errors.append("module receipt is not green")
    if receipt.get("source_sha256")!=row["source_sha256"] or receipt.get("source_sha256_after")!=row["source_sha256"]: errors.append("receipt source mismatch")
    if receipt.get("object_sha256")!=row["object_sha256"]: errors.append("receipt object mismatch")
    if receipt.get("git_head_at_launch")!=row["source_revision"]: errors.append("launch revision mismatch")
    if receipt.get("wall_seconds") is None: errors.append("missing elapsed time")
    log=(root/"evidence/lean.log").read_text()
    for ax in row["axioms"]:
        if ax not in log: errors.append(f"axiom audit lacks {ax}")
for module,row in m["direct_import_source_map"].items():
    src=root/row["source"]
    if not src.is_file() or sha(src)!=row["source_sha256"]: errors.append(f"dependency source mismatch: {module}")
# The packet is source/evidence only: never accept serialized Lean objects.
if list(root.rglob("*.olean")): errors.append("unexpected .olean in packet")
if errors:
    print("FAIL")
    print("\n".join(errors))
    sys.exit(1)
print(f"PASS: {m['packet']} ({len(m['files'])} frozen files)")
