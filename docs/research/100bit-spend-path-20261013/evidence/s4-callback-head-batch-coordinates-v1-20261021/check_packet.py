#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
for entry in m['files']:
 p=root/entry['path']
 if not p.is_file(): errors.append(f"missing file: {entry['path']}"); continue
 if sha(p)!=entry['sha256']: errors.append(f"hash mismatch: {entry['path']}")
 if p.stat().st_size!=entry['size_bytes']: errors.append(f"size mismatch: {entry['path']}")
for mod in m['modules']:
 for key in ['source','receipt','preflight','command','lean_log','time_log']:
  if not (root/mod[key]).is_file(): errors.append(f"missing module {key}: {mod[key]}")
 if sha(root/mod['source'])!=mod['source_sha256']: errors.append('module source hash mismatch')
for name,owner in m['direct_import_source_map'].items():
 p=root/owner['source']
 if not p.is_file(): errors.append(f"missing dependency snapshot: {name}")
 elif sha(p)!=owner['source_sha256']: errors.append(f"dependency source hash mismatch: {name}")
# Ensure this source-only packet contains no compiled Lean objects.
for p in root.rglob('*'):
 if p.is_file() and p.suffix in {'.olean','.ilean','.c','.o'}: errors.append(f"unexpected compiled artifact: {p.relative_to(root)}")
if errors:
 print('\n'.join(errors)); sys.exit(1)
print(f"PASS: {len(m['files'])} pinned files, {len(m['modules'])} green module, {len(m['direct_import_source_map'])} direct imports; source-only.")
