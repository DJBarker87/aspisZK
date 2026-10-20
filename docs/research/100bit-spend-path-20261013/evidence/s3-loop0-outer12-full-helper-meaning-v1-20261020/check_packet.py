#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent;m=json.loads((root/'manifest.json').read_text());errors=[]
for rel,want in m['files'].items():
 f=root/rel
 if not f.is_file():errors.append('missing '+rel);continue
 got=hashlib.sha256(f.read_bytes()).hexdigest()
 if got!=want:errors.append(f'hash {rel}: {got} != {want}')
for x in m['modules']:
 for key in ('source','receipt','command','preflight','lean_log','time_log'):
  if not (root/x[key]).is_file():errors.append(f'missing {x["module"]}:{key}')
 if (root/x['source']).is_file() and hashlib.sha256((root/x['source']).read_bytes()).hexdigest()!=x['source_sha256']:errors.append('source hash '+x['module'])
 r=json.loads((root/x['receipt']).read_text())
 if r.get('exit_status')!=0 or r.get('source_sha256')!=x['source_sha256'] or r.get('object_sha256')!=x['object_sha256']:errors.append('receipt mismatch '+x['module'])
 if r.get('scope_swap_peak_bytes')!=0:errors.append('swap '+x['module'])
 if set(x['axioms'])!={'propext','Classical.choice','Quot.sound'}:errors.append('axioms '+x['module'])
if errors:print('FAIL\n'+'\n'.join(errors));sys.exit(1)
import subprocess
subprocess.run([sys.executable,str(root/'check_public_recurrence_adapter.py')],check=True)
print(f'PASS: {len(m["modules"])} module receipts; {len(m["files"])} file hashes')
