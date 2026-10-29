"""Check evidence integrity only. No Lean, native build, or manifest replay."""
from pathlib import Path
import json,subprocess,hashlib,collections,re
D=Path(__file__).resolve().parent;P=D.parent/'pv-mfc-20261029';load=lambda p:json.load(open(p));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=load(P/'classifications.json');new=load(D/'classifications.json');s=load(D/'summary.json');runs=load(D/'runs.json');inp=load(D/'next-input.json')
assert len(old)==len(new)==764 and [r['input'] for r in new]==[r['input'] for r in old]
assert dict(collections.Counter(r['category'] for r in new))==s['counts']=={'A':76,'B':657,'C':31}
resumed=[r for r in new if old[r['record']-1]['category']=='C'];assert len(resumed)==132
assert dict(collections.Counter(r['category'] for r in resumed))==s['resumed_132']=={'A':55,'B':46,'C':31}
assert [r['attempt'] for r in runs]==list(range(70000,70100))
assert len(runs)==s['lean_invocations']==100 and all(r['exit']==0 for r in runs)
assert not any(r['elaboration_failed'] or r['environment_failed'] for r in runs)
checks={r['row']:r for r in runs if r['mode']=='check'};assert set(checks)=={'V243','V260','V195','V219','V246'}
assert sum(r['mode']=='rebuild' for r in runs)==95
for r in runs:
 O=D/f"lean-{r['attempt']}";q=load(O/'receipt/receipt.json');pre=load(O/'preflight.json')
 assert q['exit_status']==r['exit']==0 and q['swaps']==0
 assert q['source_revision']==r['source_revision']==pre['source_revision']==inp['source_revision']
 assert q['source_sha256']==r['source_sha256']==pre['source_sha256']
 assert q['print_axioms']==r['axioms']
 assert q['dependencies_sha256']==hashlib.sha256(json.dumps(pre,sort_keys=True).encode()).hexdigest()
 assert pre['external_objects_checked']==5673
 for name in ['admission.json','barrier.json']:assert load(O/name)['allowed'] is True
 assert q['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for a in r['axioms']:
  assert 'sorryAx' not in a
  if 'depends on axioms: [' in a:assert set(filter(None,re.split(r',\s*',re.search(r'\[([^\]]*)\]',a)[1])))<=set(['propext','Classical.choice','Quot.sound'])
 if r['mode']=='rebuild':
  v=inp['modules'][r['module']];raw=subprocess.check_output(['git','show','HEAD:'+v['path']]);assert hashlib.sha256(raw).hexdigest()==v['sha256']==r['source_sha256']
 else:
  assert sha(D/'checks'/('PV_MF_'+r['row']+'.lean'))==r['source_sha256']
  assert len(r['axioms'])==1 and '[propext, Classical.choice, Quot.sound]' in r['axioms'][0]
 for m,v in pre['private_imports'].items():
  assert inp['modules'][m]['sha256']==v['source_sha256']
  if v['attempt']>=70000:
   prev=next(x for x in runs if x['attempt']==v['attempt']);assert prev['object_sha256']==v['object_sha256'] and prev['attempt']<r['attempt']
  else:
   prev=load(P/f"lean-{v['attempt']}/result.json");assert prev['exit']==0 and prev['object_sha256']==v['object_sha256']
for r in new:
 assert r['reason']
 assert subprocess.check_output(['git','rev-parse','HEAD:'+r['input']['path']],text=True).strip()==r['current_blob']
 o=old[r['record']-1]
 if o['category']!='C':assert r==o
 elif r['category']=='A':assert r['credited_rows']==['V243'] and r['result']=='PASSES' and r['check']==checks['V243']['receipt']
 elif r['category']=='C':assert r['result']=='NOT RUN' and 'cohort' in r['reason']
nat=load(D/'native-chains.json');prev=load(P/'native-chains.json');assert len(nat['records'])==58
assert all(r['category']=='B' for r in nat['records'])
assert [(r['record'],r['input'],r['pointer_payload']) for r in nat['records']]==[(r['record'],r['input'],r['pointer_payload']) for r in prev['records']]
for f in nat['evidence_files']:
 raw=subprocess.check_output(['git','show','HEAD:'+f['path']]);assert hashlib.sha256(raw).hexdigest()==f['sha256']
for f in nat['current_body_pins_verified']:
 raw=subprocess.check_output(['git','show','HEAD:'+f['path']]);assert hashlib.sha256(raw).hexdigest()==f['sha256']
assert len(load(D/'rebuild-frontier.json')['pending_jobs'])==20
assert s['native_scopes']==s['kani']==0 and s['complete'] is False and not s['failing_credited_closures']
assert s['guard_sha256']==sha(D/'PV_MF_rebuild_host.py')
changed=subprocess.check_output(['git','diff','--name-only','212f9c5a54'],text=True).splitlines();assert all(p.startswith('evidence/pv-mfd-20261029/') for p in changed)
for p in D.rglob('*'):
 if not p.is_file() or 'sources' in p.relative_to(D).parts:continue
 assert p.stat().st_size<=20*1024*1024,p
 assert p.suffix not in ['.olean','.ilean','.elf','.tar'],p
 if p.suffix=='.lean':assert p.name.startswith('PV_MF_') and all(l.startswith(('import ','#check ','#print axioms ')) for l in p.read_text().splitlines())
(D/'validation.json').write_text(json.dumps(dict(integrity='PASS',records=764,counts=s['counts'],resumed_132=s['resumed_132'],lean_invocations=100,passed_checks=list(checks),native_scopes=0,kani=0,no_source_edits=True,no_proofs=True,no_manifest_replay=True,complete=False),indent=2)+'\n')
print((D/'validation.json').read_text())
