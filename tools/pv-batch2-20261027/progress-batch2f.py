"""Collect only accepted current sources and preserve all refused/failed attempts."""
from pathlib import Path
import json,hashlib,datetime,subprocess
E=Path('evidence/pv-batch2-20261027/batch2f');L=Path('docs/research/v8-r0-zk-20261009/lean');t=json.loads((E/'TALLY.json').read_text());receipts=[];holds=[];accepted={}
for a in t['attempts']:
 p=E/(str(a['id'])+'.json')
 if p.exists():
  r=json.loads(p.read_text());receipts.append(r)
  if r['exit_status']==0 and r['accepted_axioms']:
   q=L/(r['module']+'.lean');sha=hashlib.sha256(q.read_bytes()).hexdigest()
   if sha==r['source_sha256']:accepted[r['module']]=dict(module=r['module'],path=str(q),source_sha256=sha,attempt=r['attempt'],declarations=r['parsed_axioms'])
 else:
  a['charged']=False
  h=E/(str(a['id'])+'-reservation.log')
  if h.exists():
   r=json.loads(h.read_text());a['uncharged_reason']='ordinary outer reservation hold; compiler not launched';holds.append(dict(id=a['id'],utc=r['utc'],allowed=r['allowed'],retry_after_epoch=datetime.datetime.fromisoformat(r['utc']).timestamp()+180))
t['used_ids']=[a['id'] for a in t['attempts']];t['next_id']=max(t['used_ids'])+1;t['remaining_lean_budget']=60-t['lean_charged'];(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
(E/'LEAN-RECEIPTS.json').write_text(json.dumps(receipts,indent=2)+'\n');(E/'ADMISSION-HOLDS.json').write_text(json.dumps(holds,indent=2)+'\n')
(E/'ACCEPTED-PROGRESS.json').write_text(json.dumps(dict(sources=list(accepted.values()),failed=[r['attempt'] for r in receipts if r['exit_status']!=0],axiom_policy=['propext','Classical.choice','Quot.sound']),indent=2)+'\n')
print('charged',t['lean_charged'],'accepted modules',len(accepted),'uncharged holds',len(holds))
