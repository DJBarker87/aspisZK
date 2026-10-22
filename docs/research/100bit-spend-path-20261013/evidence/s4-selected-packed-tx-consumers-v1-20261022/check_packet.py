#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
pre=json.loads((root/'receipt/preflight.json').read_text())
rec=json.loads((root/'receipt/receipt.json').read_text())
src=root/'sources/S4SelectedPackedTxConsumersV1.lean'
assert sha(src)==pre['source_sha256']==rec['source_sha256']
assert rec['exit_status']==0 and rec['object_sha256']=='a58e4986a611472880b3e743f359db5b530d294eca3d5ccf4fc99caf7f881155'
assert rec['revision_at_launch']==pre['source_revision']=='29b4fd270a640a9cd82a9e5ef6d82e09297c19df' and rec['swaps']==0
log=(root/'receipt/lean.log').read_text()
for name in ['tx1_success_ten_selected_packed_batches','tx2_success_twelve_selected_packed_batches']:
 assert f"AspisR1.S4SelectedPackedTxConsumersV1.{name}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
text=src.read_text()
for name in ['tx1_success_ten_selected_packed_batches','tx2_success_twelve_selected_packed_batches']:
 assert f'theorem {name}' in text and f'#print axioms {name}' in text
assert 'sorry' not in text and not list(root.rglob('*.olean'))
preDirect=json.loads((root/'receipt/direct-owner-pins.json').read_text())
for name,row in preDirect.items():
 obj=Path(row['object_path']); assert obj.is_file() and sha(obj)==row['object_sha256'],name
 snap=root/row['snapshot']; assert sha(snap)==row['source_sha256'],name
profile=root/'receipt/complete-profile.txt'
assert sha(profile)==pre['profile_sha256']
closure=json.loads((root/'receipt/olean-import-closure.json').read_text())
assert closure['modules']==7531 and closure['missing']==[]
assert rec['object_sha256'] and pre['lean_sha256']==sha(Path(pre['lean']))
print('S4 selected packed tx-consumer packet: PASS')
