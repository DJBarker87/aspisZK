"""Hash deterministic records and ledger bytes after the inherited gate succeeds."""
from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-integ4-20261027/combined');O=H/'corpus-6000';rows=[]
s=json.loads((O/'pipeline-final.json').read_text());assert s['complete'] and s['passed'] and s['completed_pairs']==1000
sha=lambda b:hashlib.sha256(b).hexdigest()
for seed in range(6000,7000):
 a=O/f'{seed}-baseline/{seed}';b=O/f'{seed}-candidate/{seed}'
 raw=[(p/'result.json').read_bytes() for p in [a,b]];rec=[json.loads(x) for x in raw]
 canon=[json.dumps({k:v for k,v in r.items() if k!='seconds'},sort_keys=True,separators=(',',':')).encode() for r in rec]
 assert canon[0]==canon[1],seed
 ledgers=[]
 for d in [a,b]:ledgers.append({p.name:dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted((d/'ledger').iterdir())})
 assert ledgers[0]==ledgers[1],seed
 r=json.loads((O/f'comparison-{seed}.json').read_text());assert r['passed']
 rows.append(dict(seed=seed,raw_record_sha256=[sha(x) for x in raw],raw_record_identical=raw[0]==raw[1],canonical_record_sha256=sha(canon[0]),canonical_byte_identical=True,ledger=ledgers[0]))
assert not any(p.exists() for p in [H/'combined-quiet-001',H/'combined-quiet-001-results'])
(H/'record-ledger-audit.json').write_text(json.dumps(dict(passed=True,records=1000,raw_records_identical=sum(r['raw_record_identical'] for r in rows),canonical_records_byte_identical=1000,ledger_pairs_identical=1000,elapsed_exclusion='seconds only; differential harness emits no seconds field',rows=rows),indent=2)+'\n')
print('PASS: 1000 canonical record and ledger pairs; quiet timing remains unrun')
