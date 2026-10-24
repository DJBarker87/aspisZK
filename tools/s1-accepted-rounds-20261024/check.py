#!/usr/bin/env python3
"""Source-only audit, no compiler, native job or private cache mutation."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-accepted-rounds-numeric-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'targets.json').read_text());pins=json.loads((E/'s1-accepted-rounds-numeric-import-pins.json').read_text());recs={}
for name,attempt in m['targets'].items():
 d=E/attempt;r=json.loads((d/'receipt.json').read_text());recs[name]=r
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert sha(S/(name+'.lean'))==sha(d/'source.lean')==r['source_sha256']==pins['targets'][name]['source_sha256']
 assert r['command'][r['command'].index('-j1')+1]=='-M4400'
 for audit in r['print_axioms']:
  matched=re.findall(r'\[(.*?)\]',audit,re.S)
  if matched:assert set(matched[0].replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(d/'source.lean').read_text())
 for dep,info in r['direct_imports'].items():
  if dep in m['targets']:
   actual=json.loads((E/m['targets'][dep]/'receipt.json').read_text())
   assert info['sha256']==actual['object_sha256'],(name,dep)
# The stronger old arithmetic predicate is definitionally equivalent, not weakened.
rounds=(S/'S1AcceptedRoundsNumericV1.lean').read_text()
assert 'Canonical q ↔ AspisS1SemanticArrayRanges.Canonical q := Iff.rfl' in rounds
assert any('canonical_iff_source_ranges' in a and 'does not depend on any axioms' in a for a in recs['S1AcceptedRoundsNumericV1']['print_axioms'])
f=json.loads((P/'factor-source.json').read_text());assert sha(R/f['original'])==f['original_sha256'] and sha(R/f['factored'])==f['factored_sha256']
a=(R/f['original']).read_text().split('theorem decoded_success_inv',1)[1].split('/-- Once decoding',1)[0]
b=(R/f['factored']).read_text().split('theorem decoded_success_inv',1)[1].split('#print axioms decoded_success_inv',1)[0]
assert a==b and hashlib.sha256(a.encode()).hexdigest()==f['copied_proof_span_sha256']
reuse=json.loads((P/'reused-trace.json').read_text())
for row in reuse['modules']:
 assert sha(R/row['source'])==row['source_sha256'] and sha(R/row['producer_receipt'])==row['producer_receipt_sha256']
 producer=json.loads((R/row['producer_receipt']).read_text());assert producer['exit_status']==0 and producer['object_sha256']==row['object_sha256']
for groups in json.loads((P/'tools.json').read_text()).values():
 if isinstance(groups,dict):
  for file,h in groups.items():assert sha(R/file)==h,file
selected=set(m['targets'].values())
for row in m['attempts']:
 assert row['selected']==(row['attempt'] in selected)
 if row['exit_status']==134:
  assert not row['selected'] and 'memory_exception' in (E/row['attempt']/'time.log').read_text()
# No conflicting selected object for one module within this focused closure.
byname={}
for row in pins['modules']:
 assert row['name'] not in byname or byname[row['name']]==row['sha256'];byname[row['name']]=row['sha256']
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',**m['metrics'],selected_import_modules=len(byname),scope=m['scope'])))
