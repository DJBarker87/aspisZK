#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((r/'manifest.json').read_text()); rec=json.loads((r/'receipt/receipt.json').read_text())
s=r/'sources/ChosenModelRow31AcceptanceV1.lean'; log=(r/'receipt/lean.log').read_text()
assert sha(s)==m['source_sha256']==rec['source_sha256']
assert rec['exit_status']==0 and rec['process_swaps']==0 and rec['watchdog_abort'] is None
assert rec['object_sha256']==m['object_sha256'] and rec['wall_seconds']==38.049
assert sha(r/'receipt/LEAN_PATH.txt')==m['closure']['profile_sha256']
assert m['closure']['module_count']==6063 and m['closure']['missing']==[]
assert m['axioms']==['propext','Classical.choice','Quot.sound']
assert 'successful_queries_row31_literal_acceptance\' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]' in log
assert 'sorryAx' not in log
for pin in m['direct_imports']:
 p=Path(pin['object_path']); assert p.exists() and sha(p)==pin['object_sha256']
 if pin['source_path']:
  q=Path(pin['source_path']); assert q.exists() and sha(q)==pin['source_sha256']
assert not list(r.rglob('*.olean')) and not list(r.rglob('*.llbc'))
print('PASS')
