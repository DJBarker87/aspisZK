#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-round-canonical-cache-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
provenance=json.loads((P/'provenance.json').read_text())
assert sha(R/provenance['manifest'])==provenance['manifest_sha256']
for row in provenance['modules']:
 assert sha(R/row['source'])==row['source_sha256']
 rec=json.loads((R/row['producer_receipt']).read_text())
 assert rec['source_sha256']==row['source_sha256'] and rec['object_sha256']==row['object_sha256'] and rec['exit_status']==0
targets=json.loads((P/'targets.json').read_text())
for name,attempt in targets['targets'].items():
 d=E/attempt;r=json.loads((d/'receipt.json').read_text());assert r['target']==name and r['exit_status']==0 and r['swaps']==0
 assert sha(d/'source.lean')==r['source_sha256']==sha(B/'lean-candidates/s126-caller-boundary-20261021'/(name+'.lean'))
 assert r['print_axioms']
 for a in r['print_axioms']:
  axioms=re.findall(r'\[(.*?)\]',a,re.S)
  if axioms:assert set(axioms[0].replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(d/'source.lean').read_text())
tools=json.loads((P/'tools.json').read_text())
for group in ['files','reused']:
 for p,h in tools[group].items():assert sha(R/p)==h
pins=json.loads((E/'s1-round-canonical-import-pins.json').read_text())
for n,a in targets['targets'].items():
 assert pins['targets'][n]['source_sha256']==json.loads((E/a/'receipt.json').read_text())['source_sha256']
assert not any(p.suffix in ['.olean','.llbc','.so','.o','.a'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',reused_source_proofs=len(provenance['modules']),metrics=targets['metrics'],scope=targets['scope'])))
