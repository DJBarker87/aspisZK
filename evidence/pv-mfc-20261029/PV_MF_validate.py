"""Review/receipt integrity only. Invokes no Lean or manifest replay."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections,re
D=Path(__file__).resolve().parent;B=D.parent/'pv-mfb-20261029';load=lambda p:json.load(open(p));old=load(B/'classifications.json');new=load(D/'classifications.json');s=load(D/'summary.json');inp=load(D/'rebuild-input.json');runs=load(D/'runs.json')
assert len(new)==len(old)==764
assert [r['input'] for r in new]==[r['input'] for r in old]
assert dict(collections.Counter(r['category'] for r in new))==s['counts']
resumed=[r for r in new if old[r['record']-1]['category']=='C'];assert len(resumed)==161
assert dict(collections.Counter(r['category'] for r in resumed))==s['resumed_161']
assert [r['attempt'] for r in runs]==list(range(69800,69860))
assert len(runs)==s['lean_invocations']==60
assert len([r for r in runs if r['exit']==0])==59
assert len([r for r in runs if r.get('environment_failed')])==1
assert not any(r.get('elaboration_failed') for r in runs)
assert not s['failing_credited_closures'] and not s['complete']
checks={r['row']:r for r in runs if r['mode']=='check'};assert set(checks)=={'V211','V228'}
for row,r in checks.items():
 assert r['exit']==0 and len(r['axioms'])==1 and '[propext, Classical.choice, Quot.sound]' in r['axioms'][0]
 cs=inp['rows'][row];text='import '+cs['module']+'\n#check '+cs['theorem']+'\n#print axioms '+cs['theorem']+'\n'
 assert hashlib.sha256(text.encode()).hexdigest()==r['source_sha256']
for r in runs:
 p=D/('lean-'+str(r['attempt']));q=load(p/'receipt/receipt.json');pre=load(p/'preflight.json')
 assert q['exit_status']==r['exit'] and q['swaps']==0
 assert q['source_revision']==r['source_revision']==pre['source_revision']==inp['source_revision']
 assert q['source_sha256']==r['source_sha256']==pre['source_sha256']
 assert q['print_axioms']==r['axioms']
 assert all('sorryAx' not in a for a in r['axioms'])
 assert pre['external_objects_checked']==5673
 for name in ['admission.json','barrier.json']:assert load(p/name)['allowed'] is True
 assert q['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if r['mode']=='rebuild':
  z=inp['modules'][r['module']];raw=subprocess.check_output(['git','show','HEAD:'+z['path']]);assert hashlib.sha256(raw).hexdigest()==z['sha256']==r['source_sha256']
for r in new:
 assert r['reason']
 assert subprocess.check_output(['git','rev-parse','HEAD:'+r['input']['path']],text=True).strip()==r['current_blob']
 if old[r['record']-1]['category']!='C':assert r['category']==old[r['record']-1]['category']
 if old[r['record']-1]['category']=='C' and r['category']=='A':assert r['result']=='PASSES' and r['credited_rows'][0] in checks
nat=load(D/'native-chains.json');assert len(nat['records'])==58
assert collections.Counter(r['category'] for r in nat['records'])=={'B':12,'C':46}
for z in nat['evidence_files']:
 raw=subprocess.check_output(['git','show','HEAD:'+z['path']]);assert hashlib.sha256(raw).hexdigest()==z['sha256']
e=load(D/'environment-correction-69821.json');raw=(D/'lean-69821/result-initial.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==e['original_result_sha256'];assert 'object file' in e['exact_error'] and 'does not exist' in e['exact_error']
assert load(D/'id-collision-filtered.json')['real_attempt_collisions']==[]
assert len(load(D/'rebuild-frontier.json')['modules'])==30
changed=subprocess.check_output(['git','diff','--name-only','b0ceae89f9'],text=True).splitlines();assert all(p.startswith('evidence/pv-mfc-20261029/') for p in changed)
assert not [p for p in D.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
assert not [p for p in D.rglob('*') if p.suffix in ['.olean','.ilean','.tar','.elf']]
result=dict(integrity='PASS',records=764,counts=s['counts'],resumed=s['resumed_161'],lean_invocations=60,new_statement_checks=['V211 PASSES','V228 PASSES'],complete=False,no_source_edits=True,no_manifest_replay=True)
(D/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
