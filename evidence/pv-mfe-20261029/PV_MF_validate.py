"""Focused receipt/source integrity checks. Does not invoke a compiler."""
from pathlib import Path
import json,hashlib,subprocess,collections,re,datetime
D=Path(__file__).resolve().parent;load=lambda p:json.load(open(p));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();s=load(D/'summary.json');runs=load(D/'runs.json');old=load(D.parent/'pv-mfd-20261029/classifications.json');new=load(D/'classifications.json');tree={x.split('\t')[1]:x.split('\t')[0].split()[-1] for x in subprocess.check_output(['git','ls-tree','-r','HEAD'],text=True).splitlines()};proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE);cache={}
def source(p):
 if p not in cache:
  proc.stdin.write((tree[p]+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().split();cache[p]=proc.stdout.read(int(h[2]));proc.stdout.read(1)
 return cache[p]
assert not load(D/'compiled-authority-audit.json')['conflicts']
assert len(old)==len(new)==764
assert [r['input'] for r in old]==[r['input'] for r in new]
assert dict(collections.Counter(r['category'] for r in new))==s['counts']==dict(A=76,B=657,C=31)
for a,b in zip(old,new):
 assert tree[b['input']['path']]==b['current_blob']
 assert a['category']==b['category']
 if a['category']!='C':assert a==b
 else:assert b['result']=='NOT RUN' and 'cohort' in b['reason']
collection=load(D/'collection.json');assert collection['completed']==len(runs) and collection['original_replay_object_mismatches']==[] and not collection['task_scopes'].strip() and not collection['active_queues']
assert len(runs)==s['lean_invocations']<=80
assert len(runs)==80 or (len(s['admission_refusals'])>=11 and not load(D/'collection.json').get('active_queues'))
assert len({r['attempt'] for r in runs})==len(runs) and all(70300<=r['attempt']<=70399 for r in runs)
assert [r['attempt'] for r in runs]==sorted(r['attempt'] for r in runs)
assert sum(r['exit']==0 for r in runs)==s['lean_passes']
assert [r['attempt'] for r in runs if r['exit']] == [70320,70321,70322]
assert all(r['environment_failed'] and not r['elaboration_failed'] for r in runs if r['exit'])
gates=sorted(D.glob('lean-*/admission.json'))
for i,p in enumerate(gates[:-1]):
 refused=not load(p).get('allowed')
 bp=p.parent/'barrier.json'
 if bp.exists() and not load(bp).get('allowed'):refused=True
 if refused:
  a=datetime.datetime.fromisoformat(load(p)['utc']);b=datetime.datetime.fromisoformat(load(gates[i+1])['utc']);assert (b-a).total_seconds()>=180
for n in s['admission_refusals']:assert not (D/f'lean-{n}/result.json').exists()
assert not s['new_A'] and s['resumed_31']==dict(A=0,B=0,C=31)
mods={}
for f in ['rebuild-input.json','h5-input.json','h5-audit-input.json']:mods.update(load(D/f)['modules'])
for r in runs:
 O=D/f"lean-{r['attempt']}";q=load(O/'receipt/receipt.json');pre=load(O/'preflight.json')
 assert q['exit_status']==r['exit'] and q['swaps']==0
 assert q['source_revision']==r['source_revision']==pre['source_revision']==s['source_revision']
 assert q['source_sha256']==r['source_sha256']==pre['source_sha256']
 assert q['print_axioms']==r['axioms']
 assert pre['external_objects_checked']==5673
 assert q['dependencies_sha256']==hashlib.sha256(json.dumps(pre,sort_keys=True).encode()).hexdigest()
 for name in ['admission.json','barrier.json']:assert load(O/name)['allowed'] is True
 assert q['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for a in r['axioms']:
  assert 'sorryAx' not in a
  if 'depends on axioms: [' in a:assert set(filter(None,re.split(r',\s*',re.search(r'\[([^\]]*)\]',a)[1])))<=set(['propext','Classical.choice','Quot.sound'])
 if r['mode']=='rebuild':assert hashlib.sha256(source(mods[r['module']]['path'])).hexdigest()==r['source_sha256']
 else:
  assert r['row']=='V261' and r['exit']==0 and len(r['axioms'])==1
  j=load(D/'rebuild-input.json')['rows']['V261'];txt='import '+j['module']+'\n#check '+j['theorem']+'\n#print axioms '+j['theorem']+'\n';assert hashlib.sha256(txt.encode()).hexdigest()==r['source_sha256'];p=D/'checks/PV_MF_V261.lean';p.parent.mkdir(exist_ok=True);p.write_text(txt)
 for m,v in pre['private_imports'].items():
  assert mods[m]['sha256']==v['source_sha256']
  if v['attempt']>=70300:
   prev=next(x for x in runs if x['attempt']==v['attempt']);assert prev['exit']==0 and prev['attempt']<r['attempt'] and prev['object_sha256']==v['object_sha256']
  else:
   root=D.parent/('pv-mfc-20261029' if v['attempt']<70000 else 'pv-mfd-20261029');prev=load(root/f"lean-{v['attempt']}/result.json");assert prev['exit']==0 and prev['object_sha256']==v['object_sha256']
assert len(s['h5_endpoint_consumers_passed'])==10 and s['h5_all_consumers_complete'] is False
h=load(D/'h5-double-prime-current.json');assert h['current_candidate_sha256']==h['current_research_sha256']==h['tracked_sha256']
assert s['native_scopes']==s['kani']==0 and s['complete'] is False and s['target_established'] is False
for name,h in s['guard_sha256'].items():assert sha(D/name)==h
changed=subprocess.check_output(['git','diff','--name-only','331a54b9db'],text=True).splitlines();assert all(p.startswith('evidence/pv-mfe-20261029/') for p in changed),changed
for p in D.rglob('*'):
 if not p.is_file():continue
 assert p.stat().st_size<=20*1024*1024,p
 assert p.suffix not in ['.olean','.ilean','.elf','.tar','.gz','.xzbin'],p
 if p.suffix=='.lean':
  if 'audit-sources' in p.parts:
   assert sha(p)==mods['.'.join(p.relative_to(D/'audit-sources').with_suffix('').parts)]['sha256']
  else:assert p.name.startswith('PV_MF_') and all(l.startswith(('import ','#check ','#print axioms ')) for l in p.read_text().splitlines())
(D/'validation.json').write_text(json.dumps(dict(integrity='PASS',records=764,counts=s['counts'],lean_invocations=len(runs),lean_passes=s['lean_passes'],environment_failures=s['environment_failures'],new_A=0,complete=False,no_proofs=True,no_source_edits=True,no_manifest_replay=True),indent=2)+'\n');print((D/'validation.json').read_text())
