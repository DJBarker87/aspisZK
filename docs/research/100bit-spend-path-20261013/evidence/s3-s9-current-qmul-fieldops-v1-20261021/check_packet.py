#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parent
manifest=json.loads((root/"manifest.json").read_text())
errors=[]
for item in manifest.get("files", []):
 p=root/item["path"]
 if not p.is_file(): errors.append(f"missing {item['path']}"); continue
 data=p.read_bytes(); sha=hashlib.sha256(data).hexdigest()
 if sha!=item["sha256"]: errors.append(f"sha mismatch {item['path']}: {sha}")
 if len(data)!=item["size_bytes"]: errors.append(f"size mismatch {item['path']}")
for m in manifest.get("modules", []):
 p=root/m["source"]
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=m["source_sha256"]:
  errors.append(f"module source mismatch {m['module']}")
 r=root/m["receipt"]
 if not r.is_file(): errors.append(f"module receipt missing {m['module']}")
 else:
  d=json.loads(r.read_text())
  if d.get("exit_status")!=0 or d.get("source_sha256")!=m["source_sha256"]:
   errors.append(f"module receipt mismatch {m['module']}")
if errors:
 print("FAIL"); print("\n".join(errors)); sys.exit(1)
print("PASS: source, receipt, and packet file hashes")
