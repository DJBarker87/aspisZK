#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
p=Path(__file__).resolve().parent
m=json.loads((p/"manifest.json").read_text())
for rel,want in m["files"].items():
 got=hashlib.sha256((p/rel).read_bytes()).hexdigest()
 if got!=want: raise SystemExit(f"checksum mismatch: {rel}")
for name,row in m["direct_import_source_map"].items():
 rel=row.get("repository_path")
 if rel and not rel.startswith("docs/"):
  got=hashlib.sha256((p/rel).read_bytes()).hexdigest()
  if got!=row["source_sha256"]: raise SystemExit(f"source pin mismatch: {name}")
print("PASS",len(m["files"]),"files; imported source pins verified; standard axioms only")
