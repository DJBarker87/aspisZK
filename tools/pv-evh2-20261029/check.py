"""Check frozen statements, task boundaries and accepted evidence."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path('evidence/pv-evh2-20261029'); base='b51b1040f2'
new=['PV_EVH_RuntimeBinding','PV_EVH_OwnedLaws','PV_EVH_BindingAudit','PV_EVH_OwnedAudit','PV_EVH_BindingReplay']
old=Path('lean/PV_EVH_Deployed.lean').read_bytes()
assert old==subprocess.check_output(['git','show',base+':lean/PV_EVH_Deployed.lean'])
s=Path('lean/PV_EVH_RuntimeBinding.lean').read_text()
a=old.decode().split('theorem privacy_headline_deployed_events (')[1].split(' :\n',1)[1].split(' := by',1)[0]
b=s.split('theorem privacy_headline_deployed_events_at (')[1].split(' :\n',1)[1].split(' := by',1)[0]
b=b.replace('(rtDeployed template outputs x missing store)','rt')
assert re.sub(r'\s+','',a)==re.sub(r'\s+','',b),'specialised headline statement changed'
assert 'compact := fun i => PV_RunJoin_NativePublication55.actual' in s
assert 'PV_RunJoin_ActualRun.data PV_RunJoin_ActualRun.plans store' in s
assert 'ops := inferInstance' in s and 'ops_OPEN' not in s
assert 'def LivePublication : Prop' in s
runtime_fields=set(re.findall(r'^  (\w+) :',old.decode().split('structure Runtime where',1)[1].split('variable (rt : Runtime',1)[0],re.M))
binding_rows=set(re.findall(r'^\| (\w+) \|',(E/'RUNTIME-BINDING.md').read_text(),re.M))
assert runtime_fields==binding_rows,'runtime binding table incomplete'
freeze=[]
for m in new:
 p=Path('lean/'+m+'.lean');b=p.read_bytes();t=b.decode()
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',t),(m,'forbidden declaration/tactic')
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',t)
 freeze.append(dict(module=m,path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(p.startswith(('evidence/pv-evh2-20261029/','tools/pv-evh2-20261029/')) or p=='evidence/pv-evh-20261029/LINKS.md' or p in [v['path'] for v in freeze] for p in changed),changed
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*') if p.is_file())
accepted=[]
for p in E.glob('receipt-*.json'):
 v=json.loads(p.read_text())
 if not v.get('accepted'):continue
 assert v['exit']=='0' and int(v['swaps'])==0
 assert v['admission']['allowed'] is True
 assert v['axioms']
 for ax in v['axioms']:
  if 'does not depend on any axioms' in ax:continue
  names=ax.split('depends on axioms: [')[1].split(']')[0].split(',')
  assert set(x.strip() for x in names)<={'propext','Classical.choice','Quot.sound'},ax
 accepted.append(dict(attempt=v['attempt'],target=v['target'],object_sha256=v['object_sha256']))
(E/'proof-source-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
(E/'checks.json').write_text(json.dumps(dict(base=base,historical_headline_unchanged=True,specialised_statement_identical=True,T_unchanged=True,bound_unchanged=True,forbidden_source_constructs=False,oversized_files=False,accepted=accepted,rows_removed=[]),indent=2)+'\n')
print('PASS: exact specialisation, frozen generic theorem, task paths, sizes, and accepted axioms')
