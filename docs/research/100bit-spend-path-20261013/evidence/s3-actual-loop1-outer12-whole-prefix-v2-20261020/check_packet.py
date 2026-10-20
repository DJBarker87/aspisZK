#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
errors=[]
for rel,want in m.get('files',{}).items():
 f=root/rel
 if not f.is_file(): errors.append(f'missing {rel}'); continue
 got=hashlib.sha256(f.read_bytes()).hexdigest()
 if got!=want: errors.append(f'file hash mismatch {rel}: {got} != {want}')
for mod in m['modules']:
 for field in ('source','receipt','command','preflight','lean_log','time_log'):
  f=root/mod[field]
  if not f.is_file(): errors.append(f'missing {mod["module"]} {field}: {f}')
 if (root/mod['source']).is_file():
  got=hashlib.sha256((root/mod['source']).read_bytes()).hexdigest()
  if got!=mod['source_sha256']: errors.append(f'source mismatch {mod["module"]}')
 r=json.loads((root/mod['receipt']).read_text())
 if r.get('exit_status')!=0 or r.get('object_sha256')!=mod['object_sha256'] or r.get('source_sha256')!=mod['source_sha256']: errors.append(f'receipt mismatch {mod["module"]}')
 if mod['swap_peak_bytes']!=0: errors.append(f'nonzero swap {mod["module"]}')
 if set(mod['axioms'])!={'propext','Classical.choice','Quot.sound'}: errors.append(f'axiom list mismatch {mod["module"]}')
if errors:
 print('FAIL'); print('\n'.join(errors)); sys.exit(1)
print(f'PASS: {len(m["modules"])} checked modules, {len(m["files"])} file hashes')
