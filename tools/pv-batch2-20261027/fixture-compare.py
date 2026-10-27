"""Compare retained timing fixtures after source-law proofs; no new prover run."""
from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');O=H/'timing-precheck';rows=[]
for fixture in ['transfer','withdrawal']:
 for i in range(5):
  paths={who:O/who/f'sample-{i}'/f'{fixture}-{100+i}' for who in ['baseline','candidate']};files={}
  for name in ['proof.bin','public.bin']:
   bs={k:(p/name).read_bytes() if (p/name).exists() else None for k,p in paths.items()}
   files[name]=dict(identical=bs['baseline']==bs['candidate'],hashes={k:hashlib.sha256(b).hexdigest() if b is not None else None for k,b in bs.items()})
  results={k:json.loads((p/'result.json').read_text()) for k,p in paths.items()};fields=['status','attempts','callbacks','proof_sha256','audit'];same={key:results['baseline'].get(key)==results['candidate'].get(key) for key in fields}
  rows.append(dict(fixture=fixture,coin=100+i,files=files,result_fields=same))
r=dict(passed=all(all(f['identical'] for f in row['files'].values()) and all(row['result_fields'].values()) for row in rows),comparisons=rows)
(H/'fixture-comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));assert r['passed']
