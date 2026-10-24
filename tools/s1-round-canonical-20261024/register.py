#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-round-canonical-cache-20261024'
S=B/'lean-candidates/s126-caller-boundary-20261021'
names={'S1ExtractedDecodedRoundTotalV1':'s1-extracted-decoded-round-total-v1',
       'S1DecodedSampledValueTotalV1':'s1-decoded-sampled-value-total-v2'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((E/'accepted-targets.json').read_text());rs=[]
for name,attempt in names.items():
 r=json.loads((E/attempt/'receipt.json').read_text());assert r['exit_status']==0 and r['target']==name
 assert sha(S/(name+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']
 assert r['swaps']==0 and r['print_axioms'] and all('sorryAx' not in a for a in r['print_axioms'])
 m['targets'][name]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']}
 m['targets'][name]['receipt']=attempt+'/receipt.json';rs.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics=dict(targets=len(names),wall_seconds=sum(r['wall_seconds'] for r in rs),max_rss_bytes=max(r['peak_rss_bytes'] for r in rs),swaps=sum(r['swaps'] for r in rs))
(P/'targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=names,metrics=metrics,
 scope='Concrete reached decoder/sample/update implies numeric value child TOTAL and canonical result, without independent coefficient/alpha/index domains. Three reached successful source calls remain explicit; not whole parent or native SDK/abort TOTAL.'),indent=2)+'\n')
(P/'tools.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(R)):sha(p) for p in (R/'tools/s1-round-canonical-20261024').glob('*.py')},
 reused={str(p.relative_to(R)):sha(p) for p in [R/'tools/s126-sdk-20261021/lean-local.py',E/'s1-semantic-fold-controls-20261024/lean-targets.json']}),indent=2)+'\n')
print(json.dumps(metrics))
