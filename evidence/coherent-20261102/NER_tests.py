"""Check the saved Lean scan, mutation controls, cohort pins and reservation receipts."""
import copy, hashlib, json, lzma
from pathlib import Path
E=Path(__file__).resolve().parent
REPO=E.parent.parent

def archive(name):
 raw=lzma.decompress((E/(name+'.xz')).read_bytes())
 assert hashlib.sha256(raw).hexdigest()==(E/(name+'.sha256')).read_text().strip(),name
 return raw

def validate(scan, rows, manifest):
 mods={r['module']:r for r in manifest}
 assert len(rows)==len(mods)==scan['module_count']
 assert {r['module'] for r in rows}==set(mods)
 assert all(r['imports_match'] and r['imports']==mods[r['module']]['imports'] for r in rows)
 assert sum(r['edges'] for r in rows)==scan['edges']
 assert sum(r['declarations'] for r in rows)==scan['declarations']
 assert [r for r in rows if r['dangling']]==scan['dangling_modules']
 return True

scan=json.loads((E/('NER_SCAN_PRE_REBUILD.json' if (E/'NER_SCAN_PRE_REBUILD.json').exists() else 'NER_SCAN.json')).read_text())
rows=[json.loads(l) for l in archive('NER_SCAN_ROWS.jsonl').splitlines()]
manifest=[json.loads(l) for l in archive('NER_MANIFEST.jsonl').splitlines()]
assert validate(scan,rows,manifest)
pins=json.loads((REPO/'evidence/native-reconcile2-20261028/NDR_FINAL_COHORT_PINS.json').read_text())
expected={r['module']:r['object_sha256'] for r in pins['entries']}
assert set(expected)|{'NDR_CombinedAudit'}=={r['module'] for r in manifest}
assert all(r['artifacts'][0]['sha256']==expected[r['module']] for r in manifest if r['module'] in expected)
index=[json.loads(l) for l in archive('NER_COHORT.jsonl').splitlines()]
known=set(archive('NER_KNOWN.txt').decode().splitlines())
assert known=={n for r in index for n in r['names']}
assert sum(len(r['names']) for r in index)==scan['declarations']
fixture=[json.loads(l) for l in (E/'NER_FIXTURE_ROWS.jsonl').read_text().splitlines()]
assert fixture[0]['dangling']==[{'parent':'NER_Plant.parent','missing':'NER_Plant.missing'}]
assert fixture[1]['dangling']==[]
assert all(r['imports_match'] for r in fixture)
drift=json.loads((E/'NER_DRIFT_ROWS.jsonl').read_text())
assert drift['imports_match'] is False and drift['dangling']==[]
for mutation in ['omit_module','hide_dangling','wrong_import']:
 changed=copy.deepcopy(rows)
 if mutation=='omit_module':changed.pop()
 elif mutation=='hide_dangling':next(r for r in changed if r['dangling'])['dangling']=[]
 else:changed[0]['imports']=[]
 try:validate(scan,changed,manifest)
 except AssertionError:pass
 else:raise AssertionError('accepted '+mutation)
loaded=[json.loads(l) for l in (E/'NER_LOADED_fixtures.jsonl').read_text().splitlines()]
assert [(r['module'],r['dangling']) for r in loaded if r['dangling']]==[('NER_PlantObject',[{'parent':'NER_Plant.parent','missing':'NER_Plant.missing'}])]
assert all(r['imports_match'] for r in loaded)
assert next(r for r in loaded if r['module']=='NER_PlantControl')['dangling']==[]
for path in sorted(E.glob('NER_R*/receipt.json')):
 r=json.loads(path.read_text())
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command']
 for name,digest in r['source_hashes'].items():
  assert hashlib.sha256((path.parent/'sources'/name).read_bytes()).hexdigest()==digest
 a=r['attempt'];ad=json.loads((E/(a+'-reservation-0.json')).read_text())
 assert ad['allowed'] is True
 admissions=[json.loads(l) for l in (E/'NER_ATTEMPTS.jsonl').read_text().splitlines()]
 assert any(x['attempt']==a and x['event']=='admission' and x['exit']==0 for x in admissions)
plan=json.loads((E/'NER_REBUILD_PLAN.json').read_text())
assert plan['required_modules']==len(plan['modules'])==1387
assert all(r['status']=='source_located' for r in plan['modules'])
assert [r['module'] for r in plan['modules']]==scan['rebuild_order']
outputs=json.loads((E/'NER_REBUILT_OBJECT_PINS.json').read_text())
assert len(outputs)==5
for r in outputs:
 assert hashlib.sha256((E/(r['module']+'.lean')).read_bytes()).hexdigest()==r['source_sha256']
 assert r['source_sha256']==next(p['source_sha256'] for p in plan['modules'] if p['module']==r['module'])
for a in ['NER_R020','NER_R021','NER_R022','NER_R023','NER_R024']:
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0
 assert r['print_axioms']
 for item in r['deps_fingerprint']['selected_objects'].values():
  for output in outputs:
   if item['path']==output['path']:assert item['sha256']==output['sha256']
axioms=json.loads((E/('NER_AXIOMS_FOCUSED.json' if (E/'NER_AXIOMS_FOCUSED.json').exists() else 'NER_AXIOMS.json')).read_text())
assert axioms['final_agg16_runs']==0
assert all(r['raw_complete'] is None and r['equal'] is None for r in axioms['roots'])
assert len(axioms['focused'])==3
for row in axioms['focused']:
 assert row['raw_complete'] and row['equal']
 assert row['walked_axioms']==row['collect_axioms']==['Classical.choice','Quot.sound','propext']
 r=json.loads((E/row['receipt']).read_text());assert r['exit_status']==0
 assert len((E/('NER_focused_'+{'AspisR1.JGx_SdkAfterValidationEq.source':'sdk','AspisR1.JFw_Validator.loop_valid':'validator','AspisR1.JFw_Record.success':'record'}[row['root']]+'_REACHABLE.txt')).read_text().splitlines())==row['reachable_constants']
assert (E/'NER_Walker.lean').read_bytes()==(REPO/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes()
result=dict(valid=True,scope='historical original serialized cohort and focused receipts',modules=len(rows),standard_table_mutation=True,body_removal_control=True,import_drift_detected=True,negative_validator_controls=3,ndr_object_pins=len(expected),dangling_modules=[r['module'] for r in rows if r['dangling']])
(E/'NER_TEST_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
