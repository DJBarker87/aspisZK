#!/usr/bin/env python3
from pathlib import Path
import tarfile,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/source-typed-actual-first-20261018';m=json.loads((E/'packet-manifest.json').read_text());p=E/m['archive'];sha=lambda b:hashlib.sha256(b).hexdigest();digest=lambda v:sha(json.dumps(v,sort_keys=True).encode());assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==m['archive_sha256']
with tarfile.open(p) as t:
 sums=json.load(t.extractfile('SHA256SUMS.json'));assert set(t.getnames())==set(sums)|{'SHA256SUMS.json'}
 for n,h in sums.items():assert hashlib.file_digest(t.extractfile(n),'sha256').hexdigest()==h,n
 load=lambda n:json.load(t.extractfile(n));get=lambda n:t.extractfile(n).read();rs=[load(n) for n in sums if n.startswith('successful-targets/')];manifest=load('sources/SOURCE-MANIFEST.json');assert len(rs)==m['targets'] and sum(len(r['axioms']['reports']) for r in rs)==m['axiom_reports']
 predecessor=load('accepted-project-predecessors.json');assert predecessor['prior_archives']==['7dbd428c81ee45c8aa631e75b075cbed7cac472c6fc559709cae65a556e3de65','bc700a9bb9e352f529ed4fd87123699a8fc4b7a56cc789384efba0646ef05409'];allrs={**predecessor['receipts'],**{r['target']:r for r in rs}};d=load('current-object-pins.json');assert len(d['modules'])==m['current_snapshot_modules']
 keys={};visiting=set()
 def key(n):
  if n in keys:return keys[n]
  assert n not in visiting,n
  visiting.add(n);v=d['modules'][n]
  k={'source':v['source_sha256'],'objects':{suffix:o['sha256'] for suffix,o in v['objects'].items()},'imports':{dep:key(dep) for dep in v['imports']},'runtime':d['runtime_files']}
  keys[n]=digest(k);visiting.remove(n);return keys[n]
 for n in d['modules']:key(n)
 for r in rs:
  assert r['exit_status']==0 and r['axioms']['passed'] and r['process_swaps']==0
  assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['axioms']['reports'])
  assert r['key']['source_sha256']==sha(get('sources/'+manifest['modules'][r['target']]['stage_as']))
  assert r['key']['source_sha256']==sha((R/'lean/bridge-source-trace-current-20261018'/manifest['modules'][r['target']]['stage_as']).read_bytes())
  for suffix,o in r['objects'].items():assert sums['objects/'+r['target']+suffix]==o['sha256']
  for n,pin in r['key']['imports'].items():
   if 'receipt_key' in pin:assert pin['receipt_key']==digest(allrs[n]['key'])
   else:assert pin['closure_key']==keys[n],(r['target'],n)
  v=d['modules'][r['target']];assert v['objects']==r['objects'] and v['source_sha256']==r['key']['source_sha256']
 body=get('sources/ExtractedSourceFirstTyped.lean').decode();assert 'FirstPaired.first_paired' in body and 'FinishCalls.finish_success' in body and 'SourceCanonicalRecovery.recover' in body
 assert 'runtime583-call equality' in m['scope'] and 'C1/C2' in m['scope']
 canonical=get('sources/ExtractedSourceCanonicalRecovery.lean').decode();assert 'tr.length = 77' in canonical and 'Read whole target' in canonical and 'badColl' in canonical
 recovery=get('sources/ExtractedSourceTypedRecovery.lean').decode();assert 'InitialWalkTrace.walk_before_next' in recovery and 'raw_decode' in recovery
 assert load('circle-leaf-current-adoption-audit.json')['module']=='ExtractedCircleCalls'
print('PASS current source typed recovery targets and standard-only exports; canonical77 observations, actual first/circle25 target, nohit and wholetrace inclusion scope explicit; no compiler invoked')
