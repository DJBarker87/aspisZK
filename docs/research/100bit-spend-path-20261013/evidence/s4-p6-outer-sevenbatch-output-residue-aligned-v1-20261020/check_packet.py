#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
errors=[]
for row in m['files']:
 p=root/row['path']
 if not p.is_file(): errors.append(f"missing {row['path']}"); continue
 b=p.read_bytes()
 if hashlib.sha256(b).hexdigest()!=row['sha256']: errors.append(f"hash mismatch {row['path']}")
 if len(b)!=row['size_bytes']: errors.append(f"size mismatch {row['path']}")
for module in m['modules']:
 p=root/module['source']
 if hashlib.sha256(p.read_bytes()).hexdigest()!=module['source_sha256']:
  errors.append(f"source mismatch {module['module']}")
 if module['exit_status']!=0: errors.append(f"nonzero {module['module']}")
 if module['axioms']!=['propext','Classical.choice','Quot.sound']:
  errors.append(f"unexpected axioms {module['module']}: {module['axioms']}")
for name,row in m['direct_import_source_map'].items():
 p=(root/row['source']).resolve()
 if not p.is_file(): errors.append(f"missing direct source {name}: {p}"); continue
 if hashlib.sha256(p.read_bytes()).hexdigest()!=row['source_sha256']:
  errors.append(f"direct source mismatch {name}")
if errors:
 print('\n'.join(errors),file=sys.stderr); sys.exit(1)
print(f"PASS: {len(m['modules'])} module(s), {len(m['files'])} file(s), {len(m['direct_import_source_map'])} direct imports")
