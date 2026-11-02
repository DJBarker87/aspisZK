"""Validate complete affected rebuild, selected import identity and matched mutations."""
import copy,hashlib,json,lzma
from pathlib import Path
E=Path(__file__).resolve().parent
plan={r['module']:r for r in json.loads((E/'NER_REBUILD_PLAN.json').read_text())['modules']}
original={r['module']:r for r in map(json.loads,lzma.open(E/'NER_MANIFEST.jsonl.xz','rt'))}
rows=[]
for r in json.loads((E/'NER_REBUILT_OBJECT_PINS.json').read_text()):
 # The historical five have standalone receipt names, mapped explicitly below.
 a={'JFw_Validator':'NER_R020','JGx_SdkAfterValidationEq':'NER_R021','JFw_Chunks':'NER_R022','JFw_BlockValidation':'NER_R023','JFw_Record':'NER_R024'}[r['module']]
 receipt=json.loads((E/a/'receipt.json').read_text())
 selected={}
 for dep in plan[r['module']]['cohort_imports']:
  key=dep.replace('.','/')+'.olean'
  obj=receipt['deps_fingerprint']['selected_objects'].get(key)
  if obj is None:
   assert dep=='Init'  # Implicit Init is absent from the old runner's textual import pins.
   obj=original[dep]['artifacts'][0]
  selected[dep]={'path':obj['path'],'sha256':obj['sha256']}
 rows.append({**r,'object_sha256':r['sha256'],'exit_status':receipt['exit_status'],'selected_imports':selected,'scope':a})
for p in sorted(E.glob('NER_B*-details/modules.jsonl')):
 for line in p.read_text().splitlines():rows.append({**json.loads(line),'scope':p.parent.name.removesuffix('-details')})

def validate(rows):
 assert len(rows)==len(plan)==1387
 assert len({r['module'] for r in rows})==len(rows)
 final={r['module']:r['object_sha256'] for r in rows}
 for r in rows:
  n=r['module'];assert r['exit_status']==0,n
  assert r['source_sha256']==plan[n]['source_sha256'],n
  assert set(r['selected_imports'])==set(plan[n]['cohort_imports']),n
  for dep,pin in r['selected_imports'].items():
   expected=final.get(dep,original[dep]['artifacts'][0]['sha256'])
   assert pin['sha256']==expected,(n,dep,pin['sha256'],expected)
 return final
final=validate(rows)
mutated=copy.deepcopy(rows)
r=next(r for r in mutated if any(dep in final for dep in r['selected_imports']))
dep=next(dep for dep in r['selected_imports'] if dep in final)
r['selected_imports'][dep]['sha256']='0'*64
try:validate(mutated)
except AssertionError:pass
else:raise AssertionError('accepted planted stale-import hash')
for p in sorted(E.glob('NER_B*/receipt.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 for name,digest in r['source_hashes'].items():assert hashlib.sha256((p.parent/'sources'/name).read_bytes()).hexdigest()==digest
 a=r['attempt'];admissions=[json.loads(l) for l in (E/'NER_ATTEMPTS.jsonl').read_text().splitlines()]
 assert any(x['attempt']==a and x['event']=='admission' and x['exit']==0 and json.loads((E/x['receipt']).read_text())['allowed'] is True for x in admissions)
result={'complete':True,'modules':len(rows),'selected_affected_imports_match_final':True,'stale_import_mutation_rejected':True,'batch_scopes':len(list(E.glob('NER_B*/receipt.json')))}
(E/'NER_REBUILD_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'NER_REBUILD_ROWS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps(result))
