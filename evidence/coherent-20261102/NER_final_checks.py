"""Validate the saved final coherent scan, raw audit, cohort and matched controls."""
import hashlib,json,lzma
from pathlib import Path
E=Path(__file__).resolve().parent
def lines(name):
 p=E/name
 if p.exists():return [json.loads(l) for l in p.read_text().splitlines()]
 b=lzma.decompress((E/(name+'.xz')).read_bytes())
 assert hashlib.sha256(b).hexdigest()==(E/(name+'.sha256')).read_text().strip()
 return [json.loads(l) for l in b.splitlines()]
def read(name):return json.loads((E/name).read_text())
cohort=lines('NER_STREAM_B_COHORT.jsonl');original=lines('NER_MANIFEST.jsonl');rows=lines('NER_LOADED_final.jsonl')
assert len(cohort)==len(original)==len(rows)==16058
assert {r['module'] for r in cohort}=={r['module'] for r in original}=={r['module'] for r in rows}
assert sum(r['rebuilt'] for r in cohort)==1387
assert all(len(r['source_sha256'])==len(r['object_sha256'])==64 for r in cohort)
assert all(r['imports_match'] and not r['dangling'] for r in rows)
imports={r['module']:r['imports'] for r in original}
pins={r['module']:r for r in lines('NER_PREAGG_OBJECTS.jsonl') if r['module'] is not None}
assert len(pins)==16058
for r in cohort:
 if r['module']!='NDR_CombinedAudit':
  assert r['object_sha256']==pins[r['module']]['artifacts'][0]['sha256']
  assert r['object_path']==pins[r['module']]['artifacts'][0]['path']
  assert {a['path']:a['sha256'] for a in r['companions']}=={a['path']:a['sha256'] for a in pins[r['module']]['artifacts'][1:]}
assert all(r['imports']==imports[r['module']] for r in rows)
assert all(r['imports']==imports[r['module']] for r in cohort)
scan=read('NER_SCAN.json');assert scan['status']=='coherent'
assert scan['dangling_modules']==[] and scan['imports_all_match'] is True
assert scan['declarations']==sum(r['declarations'] for r in rows)
assert scan['edges']==sum(r['edges'] for r in rows)
r=read('NER_A900/receipt.json')
assert r['exit_status']==0 and r['swaps']=='0'
assert r['limits']=={'memory.high':'15032385536','memory.max':'17179869184','memory.swap.max':'0','pids.max':'64'}
assert any(x['attempt']=='NER_A900' and x['event']=='admission' and x['exit']==0 and read(x['receipt'])['allowed'] is True for x in lines('NER_ATTEMPTS.jsonl'))
for name,digest in r['source_hashes'].items():assert hashlib.sha256((E/'NER_A900/sources'/name).read_bytes()).hexdigest()==digest
aggregate=lines('NER_A900-details/modules.jsonl');assert len(aggregate)==1 and aggregate[0]['exit_status']==0
assert aggregate[0]['module']=='NDR_CombinedAudit' and '-M15000' in aggregate[0]['command']
assert aggregate[0]['object_sha256']==next(x['object_sha256'] for x in cohort if x['module']=='NDR_CombinedAudit')
ax=read('NER_AXIOMS.json');assert ax['final_agg16_runs']==1
assert {x['root'] for x in ax['roots']}=={'AspisR1.RPx_Deployed.deployed','AspisR1.NDR_CombinedAudit.sourceOnHeadline'}
log=(E/'NER_A900/stdout.log').read_text()
assert 'NER_PREAGG_PINS_VERIFIED' in log and 'NER_POSTAGG_INPUTS_UNCHANGED' in log
results=[json.loads(l.split('NEP_RESULT ',1)[1]) for l in log.splitlines() if l.startswith('NEP_RESULT ')]
assert len(results)==2
for a in ax['roots']:
 assert a['raw_complete'] is True and a['equal'] is True
 assert a['walked_axioms']==a['collect_axioms']==['Classical.choice','Quot.sound','propext']
 result=next(x for x in results if x['root']==a['root'])
 for key in ['reachable_constants','edges_scanned','walked_axioms','collect_axioms','equal']:assert a[key]==result[key]
 assert any(a['root'] in p for p in r['print_axioms'])
 p=E/('NER_final_'+a['root']+'_REACHABLE.txt')
 b=lzma.decompress(p.with_suffix(p.suffix+'.xz').read_bytes()) if not p.exists() else p.read_bytes()
 assert len(b.splitlines())==a['reachable_constants']
 if not p.exists():assert hashlib.sha256(b).hexdigest()==p.with_suffix(p.suffix+'.sha256').read_text().strip()
fixtures=lines('NER_RECURSOR_TEST_ROWS.jsonl')
assert [(x['module'],d['missing']) for x in fixtures for d in x['dangling']]==[('NER_RecursorPlant','NER_RecursorMissing')]
assert all(x['imports_match'] for x in fixtures)
assert read('NER_R029/receipt.json')['exit_status']==0
assert read('NER_R030/receipt.json')['exit_status']==0
assert hashlib.sha256((E/'NER_FinalDriver.lean').read_bytes()).hexdigest()==read('NER_R030/receipt.json')['source_hashes']['NER_FinalDriver.lean']
prefix=(E/'NER_FinalDriver.lean').read_text().split('open Lean Elab Command\nunsafe def main')[0]
assert prefix==(E/'NER_ReferenceTests.lean').read_text().split('unsafe def main')[0]
assert read('NER_REBUILD_CHECKS.json')['selected_affected_imports_match_final'] is True
result={'valid':True,'modules':len(rows),'rebuilt':1387,'dangling_references':0,'all_import_lists_match':True,'recursor_mutation_detected':True,'raw_roots_complete_and_equal':2,'agg16_runs':1}
(E/'NER_FINAL_TEST_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
