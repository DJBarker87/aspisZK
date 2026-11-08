from pathlib import Path
import json,hashlib,subprocess,re
p=Path(__file__).resolve().parent
rows=[json.loads(f.read_text()) for f in sorted(p.glob('NNQ_L*/receipt.json'))]
assert 31 <= len(rows) <= 50 and {r['attempt'] for r in rows} == {f'NNQ_L{i:03d}' for i in range(1,len(rows)+1)}
accepted={r['module']:r for r in rows if r['exit_status']==0}
for r in rows:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 admission=json.loads((p/(r['attempt']+'-admission.json')).read_text())
 assert admission['exit']==0 and admission['reservation']['allowed'] is True
 disk=json.loads((p/(r['attempt']+'-disk-0.json')).read_text())
 assert disk['free'] >= 40_000_000_000
checks=[json.loads(x) for x in (p/'NNQ_ATTEMPTS.jsonl').read_text().splitlines()]
for r in rows:
 share=[x for x in checks if x.get('attempt')==r['attempt'] and x.get('event')=='share_check']
 assert share and share[-1]['host']['count'] < 6

for r in accepted.values():
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 admission=json.loads((p/(r['attempt']+'-admission.json')).read_text())
 assert admission['exit']==0 and admission['reservation']['allowed'] is True
 for audit in r['print_axioms']:
  assert 'sorryAx' not in audit,audit
  if 'depends on axioms:' in audit:
   assert set(re.search(r'\[([^]]*)\]',audit)[1].replace(' ','').replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'}
 f=p/(r['module']+'.lean')
 assert f.exists() and hashlib.sha256(f.read_bytes()).hexdigest()==next(iter(r['source_hashes'].values())),r['module']
modules=[]
for n,r in accepted.items():
 modules.append(dict(module=n,old_source_sha256=None,new_source_sha256=next(iter(r['source_hashes'].values())),accepted_attempt=r['attempt'],source_revision=r['source_revision'],object=json.loads((p/r['attempt']/'object.json').read_text())))
refs=[]
for path in ['evidence/dgo2-20261108/DGO_HOST_RECIPE.md','evidence/dgo2-20261108/DGO_O2.lean','evidence/digest-p2-20261108/DGP_HostDigest.lean']:
 old=subprocess.check_output(['git','show','HEAD:'+path]);new=Path(path).read_bytes();assert old==new
 refs.append(dict(path=path,old_sha256=hashlib.sha256(old).hexdigest(),new_sha256=hashlib.sha256(new).hexdigest(),unchanged=True))
selected={}
for r in rows:
 for path,x in r['deps_fingerprint']['selected_objects'].items():
  if path in selected:assert selected[path]==x,(path,'changed dependency')
  selected[path]=x
(p/'NNQ_PINS.json').write_text(json.dumps(dict(base_revision='953e3af13bb',continuation_base_revision=subprocess.check_output(['git','rev-parse','3060fd440cc^'],text=True).strip(),modules=modules,unchanged_reference_sources=refs,inherited_selected_objects=list(selected.values())),indent=2)+'\n')
continuation=[r for r in rows if int(r['attempt'][-3:])>=31]
summary=dict(scopes=len(rows),continuation_scopes=len(continuation),continuation_budget=20,continuation_passed=sum(r['exit_status']==0 for r in continuation),continuation_failed=sum(r['exit_status']!=0 for r in continuation),passed=sum(r['exit_status']==0 for r in rows),failed=sum(r['exit_status']!=0 for r in rows),kani=0,extraction=0,closed_recipe_items=list(range(1,11)),open_recipe_items=[],o2_proved='NNQ_O2' in accepted,condition4_proved=False,headline_credit=False,timeout_increase=False,standard_axioms_only_for_accepted=True)
(p/'NNQ_RESULTS.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
