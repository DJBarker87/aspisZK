#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((ROOT/"manifest.json").read_text()); errors=[]
for rel,want in m["files"].items():
 p=ROOT/rel
 if not p.is_file(): errors.append(f"missing {rel}")
 elif sha(p)!=want: errors.append(f"hash mismatch {rel}")
for p in ROOT.rglob("*"):
 if p.is_file() and p.suffix.lower() in {".olean",".ilean",".ir",".exe",".tar",".gz",".zip"}: errors.append(f"binary {p.relative_to(ROOT)}")
for mod in m["modules"]:
 for key in ("source","receipt","preflight","command","lean_log","time_log"):
  if not (ROOT/mod[key]).is_file(): errors.append(f"missing {mod[key]}")
if errors: print("FAIL\n"+"\n".join(errors)); sys.exit(1)
print("PASS: packet hashes, target paths, and source-only constraint")
