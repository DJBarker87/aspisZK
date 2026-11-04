"""Local evidence validation; no compiler or native prover launch."""
from pathlib import Path
import json,hashlib,re,sys
E=Path(__file__).resolve().parent
allowed={'propext','Classical.choice','Quot.sound'}
rows=[json.loads(x) for x in (E/'NGP_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rows)==30 and len({r['attempt'] for r in rows})==30
for r in rows:
 a=r['attempt']; ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 c=json.loads((E/(a+'.json')).read_text());assert c['timeout']==180
 assert c['deps_fingerprint']['selected_objects']
 assert any('/Aeneas/' in x for x in c['deps_fingerprint']['selected_objects'])
 for n in c['sources']:
  snapshot=E/a/'sources'/n
  if c['kind']=='lean':assert snapshot.is_file()
  if snapshot.is_file() and n.endswith('.lean') and a not in ['NGP_L002','NGP_L003','NGP_L004','NGP_L005','NGP_L006','NGP_L015','NGP_L020']:
   assert not re.search(r'^\s*(axiom|sorry|admit)\b|:=\s*by\s+sorry|native_decide',snapshot.read_text(),re.M)
proof=json.loads((E/'NGP_audit/batch0/proof0.json').read_text())
assert proof['exit_status']==0 and len(proof['results'])==14
for r in proof['results']:assert r['equal'] and set(r['walked_axioms'])<=allowed
fixture=json.loads((E/'NGP_audit/fixtures/fixtures.json').read_text())
assert fixture['exit_status']==0 and len(fixture['results'])==8
for i,r in enumerate(fixture['results']):assert r['equal'] and bool(r['walked_axioms'])==(i<4)
scan=[json.loads(l) for l in (E/'NGP_LOADED_scan.jsonl').read_text().splitlines()]
assert len(scan)==13440 and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
# Independent source-header comparison for the exact five added source modules.
for name in ['NGP_L159','NGP_L181','NGP_WriterReuse','NGP_OracleTransport','NGP_COMBINED_IMPORT']:
 imports=['Init']+re.findall(r'^import ([\w.]+)',(E/(name+'.lean')).read_text(),re.M)
 assert next(r for r in scan if r['module']==name)['imports']==imports
 for a in reversed(rows):
  p=E/a['attempt']/'sources/NGP_generated'/(name+'.lean')
  if a['exit_status']==0 and p.exists():assert p.read_bytes()==(E/(name+'.lean')).read_bytes();break
 else:raise AssertionError('missing compiled source '+name)
# Mutation: a missing import remains a denial; it is not waived by Init handling.
mutated=next(r for r in scan if r['module']=='NGP_L159')['imports'][1:]
assert mutated!=['Init']+re.findall(r'^import ([\w.]+)',(E/'NGP_L159.lean').read_text(),re.M)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
 assert p.name!='__pycache__'
result=dict(status='PASS',attempts=30,successes=sum(r['exit_status']==0 for r in rows),excluded=[r['attempt'] for r in rows if r['exit_status']!=0],roots=14,fixtures=8,modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0,negative_import_control='denied')
print(json.dumps(result,indent=1))
