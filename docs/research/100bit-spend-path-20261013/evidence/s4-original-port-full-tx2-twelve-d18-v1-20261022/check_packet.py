#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
for rel,expected in m['packet_files'].items():
 p=root/rel
 if not p.is_file(): errors.append(f'missing {rel}')
 elif sha(p)!=expected: errors.append(f'hash mismatch {rel}')
for p in root.rglob('*'):
 if p.is_file() and p.suffix.lower() in m['forbidden_binary_suffixes']:
  errors.append(f'binary/compiled artifact present: {p.relative_to(root)}')
for rel,status in [('receipt.json',0),('failed-attempt-1/receipt.json',1),('failed-attempt-2/receipt.json',1)]:
 d=json.loads((root/rel).read_text())
 if d.get('exit_status')!=status: errors.append(f'unexpected exit status in {rel}')
if errors: print('\n'.join(errors));sys.exit(1)
print('PASS: packet hashes, run statuses, and source-only inventory verified')
