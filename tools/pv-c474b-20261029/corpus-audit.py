"""Check every physical ledger file against the compared records, then export hashes."""
from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');O=H/'bundle/corpus-6000'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
final=json.loads((O/'pipeline-final.json').read_text());assert final['complete'] and final['completed_pairs']==1000 and final['passed']
rows=[]
for coin in range(6000,7000):
 sides={}
 for side in ['baseline','candidate']:
  p=(H/'corpus-6000' if side=='baseline' else O)/f'{coin}-{side}'/str(coin);r=json.loads((p/'result.json').read_text())
  actual={f.name:list(f.read_bytes()) for f in (p/'ledger').iterdir() if f.is_file()}
  expected=dict(r['ledger_records']);assert actual==expected,(coin,side)
  sides[side]=dict(ledger={f.name:dict(sha256=sha(f),bytes=f.stat().st_size) for f in (p/'ledger').iterdir() if f.is_file()},proof_sha256=sha(p/'proof.bin') if (p/'proof.bin').exists() else None,public_sha256=sha(p/'public.bin'),result_sha256=sha(p/'result.json'))
 assert sides['baseline']['ledger']==sides['candidate']['ledger']
 rows.append(dict(coin=coin,sides=sides,comparison_sha256=sha(O/f'comparison-{coin}.json')))
(H/'bundle/corpus-ledger-audit.json').write_text(json.dumps(dict(passed=True,physical_ledger_pairs=1000,rows=rows),indent=2)+'\n');print('CORPUS_PHYSICAL_LEDGER_AUDIT_PASS 1000',flush=True)
