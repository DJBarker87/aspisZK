#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parents[1]
m=json.loads((r/'MANIFEST.json').read_text())
for name,item in m['files'].items():
 p=r/name
 if not p.is_file() or len(p.read_bytes())!=item['bytes'] or hashlib.sha256(p.read_bytes()).hexdigest()!=item['sha256']:
  raise SystemExit(f'FAIL {name}')
print(f"PASS: {len(m['files'])} payload files")
