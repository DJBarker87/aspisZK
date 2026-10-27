"""Static receipt/packet validation; no Lean or Rust execution."""
from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent; R=P.parents[1]
receipts=[]
for f in sorted(P.glob('BEj_*/receipt.json')):
 x=json.loads(f.read_text()); x['receipt_path']=str(f.relative_to(R));receipts.append(x)
 assert x['limits']['memory.high']=='6442450944'
 assert x['limits']['memory.max']=='8589934592'
 assert x['limits']['memory.swap.max']=='0'
 assert x['limits']['pids.max']=='64'
 for name,digest in x['source_hashes'].items():
  assert hashlib.sha256((f.parent/'sources'/name).read_bytes()).hexdigest()==digest
 if x['exit_status']==0:
  for audit in x.get('print_axioms',[]):
   names=re.sub(r'\s+', '', audit.split('[')[-1].rstrip(']')).split(',') if '[' in audit else []
   assert set(names)<= {'propext','Classical.choice','Quot.sound',''},audit
assert len(receipts)<=100
accepted=[]
for f in sorted((R/'lean').glob('BEj_*.lean')):
 digest=hashlib.sha256(f.read_bytes()).hexdigest()
 matches=[x for x in receipts if x['exit_status']==0 and x['source_hashes'].get(f.name)==digest]
 assert matches,'Unvalidated current source: '+str(f)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|maxHeartbeats|maxRecDepth',f.read_text()),f
 accepted.append({'path':str(f.relative_to(R)),'source_sha256':digest,'receipt':matches[-1]['receipt_path']})
for kind in ['Top.lean.txt','statement.lean.txt']:
 assert (P/('BEj_BEFORE_'+kind)).read_bytes()==(P/('BEj_AFTER_'+kind)).read_bytes()
assert (R/'lean/Rc10_Top.lean').read_bytes()==(P/'BEj_BEFORE_Top.lean.txt').read_bytes()
changed=subprocess.check_output(['git','diff','--name-only','eb96a34d7a'],cwd=R,text=True).splitlines()
assert all(f.startswith('lean/BEj_') or f.startswith('evidence/l166-proof2-20261026/') for f in changed),changed
(P/'BEj_attempts.jsonl').write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in receipts))
summary={'compiler_attempts':len(receipts),'passed':sum(x['exit_status']==0 for x in receipts),'failed':sum(x['exit_status']!=0 for x in receipts),'wall_seconds':sum(x['wall_seconds'] for x in receipts),'maximum_peak_rss_kib':max(int(x['peak_rss_kib']) for x in receipts),'swaps':sum(int(x['swaps']) for x in receipts),'new_modules':accepted,'kani_runs':0,'package_replay':False,'release_claim':False,'root_changed':False,'ledger_delta':{'T':0,'P':0,'G':0,'C':0}}
(P/'BEj_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='new_modules'},indent=2))
