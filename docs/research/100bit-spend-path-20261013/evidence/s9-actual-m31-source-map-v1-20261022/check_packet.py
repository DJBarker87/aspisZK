#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
errors=[]
for e in m['files']:
 p=root/e['path']
 if not p.is_file(): errors.append('missing: '+e['path']); continue
 if hashlib.sha256(p.read_bytes()).hexdigest()!=e['sha256']: errors.append('hash mismatch: '+e['path'])
for p in root.rglob('*'):
 if p.is_file() and (p.suffix in {'.olean','.ilean','.pyc','.llbc','.o','.a','.so','.dylib','.exe'} or '__pycache__' in p.parts): errors.append('forbidden artifact: '+str(p.relative_to(root)))
if errors: raise SystemExit('FAIL\n'+'\n'.join(errors))
print(f'PASS {len(m["files"])} manifested proof/evidence files; no compiled objects or caches')
