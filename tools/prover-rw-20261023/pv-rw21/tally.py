from pathlib import Path
import json
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw21-20261027'
used=sorted(int(p.name.split('-')[0]) for p in e.glob('[0-9]*-input.json'))
rs=[json.loads(p.read_text()) for p in sorted(e.glob('[0-9]*-receipt.json'))]
charged=[x for x in rs if x.get('charged')]
k=[json.loads(p.read_text()) for p in sorted(e.glob('pv-rw21-kani-*/charge.json'))]
x=dict(used_ids=used,next_unused_id=max(used,default=37699)+1,lean_charged=len(charged),lean_passes=sum(v.get('exit_status')==0 for v in charged),lean_failures=sum(v.get('exit_status')!=0 for v in charged),lean_remaining=100-len(charged),final_audit_reserved_attempts=3,kani_charged=len(k),kani_remaining=10-len(k),kani_harnesses=[v['harness'] for v in k],source_base='0242bd9221eb87dac8906ccbcac6d34ab1a9d2a2')
assert len(charged)<=100 and len(k)<=10
(e/'TALLY.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
