"""Validate the frozen source manifest and record reused and fresh receipts."""
from pathlib import Path
import json,hashlib,re
root=Path(__file__).resolve().parents[2];e=root/'evidence/pv-cb3-20261026';lean=root/'docs/research/v8-r0-zk-20261009/lean'
plan=json.loads((e/'RESUME_FINAL_MANIFEST_PLAN.json').read_text());receipts=[]
for p in e.glob('35*.json'):
 if re.fullmatch(r'35[678]\d\d.json',p.name):
  r=json.loads(p.read_text())
  if 'axioms' in r:receipts.append(r)
result=[]
for item in plan['reuse_checked']+plan['missing_need_compile']:
 module=item['module'];p=lean/(module.replace('.','/')+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==item['source_sha256'],module
 good=[r for r in receipts if r['module'].replace('/','.')==module and r['exit']==0 and r['source_sha256']==sha];assert good,module
 r=good[-1];assert not r.get('dependency_identity_changed_during_run'),module
 result.append(dict(module=module,attempt=r['attempt'],source_sha256=sha,receipt=str(r['attempt'])+'.json',reused='attempt' in item))
assert len(result)==39
(e/'RESUME_FINAL_MANIFEST.json').write_text(json.dumps(dict(modules=result,all_checked=True,scope='Frozen39 callback/helper closure only; new source audit separately recorded.'),indent=2)+'\n')
print('Frozen39 source/receipt identities valid')
