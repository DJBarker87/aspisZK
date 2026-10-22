#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
err=[]
for line in (root/'SHA256SUMS').read_text().splitlines():
 h,rel=line.split('  ',1); p=root/rel
 if not p.is_file() or sha(p)!=h: err.append('checksum mismatch/missing '+rel)
m=json.loads((root/'manifest.json').read_text()); r=json.loads((root/m['receipt']).read_text()); c=json.loads((root/'dependencies/closure.json').read_text())
if m['schema']!='focused-extractor-proof-packet-v1': err.append('schema mismatch')
if r['exit_status']!=0 or r['watchdog_abort'] is not None: err.append('Lean receipt not green')
if r['source_sha256']!=m['source_sha256'] or r['object_sha256']!=m['object_sha256']: err.append('source/object pin mismatch')
if c['missing'] or c['modules']!=m['closure_modules']: err.append('import closure mismatch')
if sha(root/'dependencies/full-profile.txt')!=m['lean_path_sha256']: err.append('profile hash mismatch')
if sha(root/'dependencies/closure.json')!=m['closure_sha256']: err.append('closure hash mismatch')
s=(root/'sources/QueryFinishAcceptedBridgeV1.lean').read_text()
for t in ['theorem finish_success_accepted_values','finish_success_iff','q22StateOf s','#print axioms finish_success_accepted_values']:
 if t not in s: err.append('source missing '+t)
if 'sorry' in s or 'admit' in s: err.append('sorry/admit token in source')
log=(root/'receipts/lean.log').read_text()
if 'sorryAx' in log: err.append('sorryAx in axioms report')
for x in m['axioms']:
 if x not in log: err.append('axiom absent: '+x)
pins=json.loads((root/'dependencies/direct-import-pins.json').read_text())['imports']
if len(pins)!=2: err.append('expected two direct import pins')
if err: print('\n'.join(err)); sys.exit(1)
print('PASS: same-state finish return equals q22 accepted values; source-only packet, complete import closure, standard axioms.')
