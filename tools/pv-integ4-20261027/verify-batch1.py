"""Verify scratch counts did not change fixture outputs and sources were restored."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-integ4-20261027');O=D/'batch1-counts';rows=[]
assert all(json.loads((O/'restored.json').read_text()).values())
for fixture in ['transfer','withdrawal']:
 a=D/f'fixtures-candidate/{fixture}-0';b=O/f'fixtures/{fixture}-0'
 ar=json.loads((a/'result.json').read_text());br=json.loads((b/'result.json').read_text())
 counts=br.pop('batch1_counts_230_254_258');elapsed=[ar.pop('seconds'),br.pop('seconds')]
 assert ar==br,(fixture,ar,br)
 parts={}
 for name in ['public.bin','proof.bin']:
  x=(a/name).read_bytes();y=(b/name).read_bytes();assert x==y
  parts[name]=dict(sha256=hashlib.sha256(x).hexdigest(),bytes=len(x),byte_identical=True)
 ledger={}
 assert sorted(p.name for p in (a/'ledger').iterdir())==sorted(p.name for p in (b/'ledger').iterdir())
 for p in (a/'ledger').iterdir():
  x=p.read_bytes();assert x==(b/'ledger'/p.name).read_bytes();ledger[p.name]=hashlib.sha256(x).hexdigest()
 rows.append(dict(fixture=fixture,counts_230_254_258=counts,canonical_record_identical=True,elapsed_seconds=elapsed,files=parts,ledger_sha256=ledger))
(O/'fixture-equivalence.json').write_text(json.dumps(dict(passed=True,rows=rows),indent=2)+'\n')
print('PASS: counter fixtures match pinned candidate bytes and canonical records; scratch sources restored')
