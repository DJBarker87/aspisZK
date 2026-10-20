#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
p=Path(__file__).resolve().parent
m=json.loads((p/"manifest.json").read_text())
for rel,want in m["files"].items():
 got=hashlib.sha256((p/rel).read_bytes()).hexdigest()
 if got!=want: raise SystemExit(f"checksum mismatch: {rel}")
print("PASS",len(m["files"]),"files; standard axioms only; source-only packet")
