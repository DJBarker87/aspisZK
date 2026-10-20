#!/usr/bin/env python3
"""Check existing successful focused receipts; never recompile unchanged proofs."""
from pathlib import Path
import hashlib,json,re,subprocess
B=Path(__file__).resolve().parents[3];E=B/'evidence/stage2-continuation-20261020';objects=Path('/tmp/codex-cx-stage2b-20261020-objects');rows=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p in sorted((B/'lean').glob('Stage2Continuation*.lean')):
 candidates=[]
 for q in (E/'proofs').glob('*/receipt.json'):
  r=json.loads(q.read_text())
  if r['module']==p.stem and r['exit_status']==0 and r['source_sha256']==sha(p):candidates.append((q.stat().st_mtime,q,r))
 assert candidates,p
 _,q,r=max(candidates)
 for name,imp in r['direct_imports'].items():assert sha(Path(imp['object_path']))==imp['sha256'],(p,name,'dependency changed')
 assert not any('sorryAx' in a for a in r['print_axioms']),p
 theorems=set(re.findall(r'^(?:private )?theorem (\w+)',p.read_text(),re.M));audits=set(re.findall(r'^#print axioms (\w+)',p.read_text(),re.M));assert theorems<=audits,p
 for word in ['sorry','axiom','admit','native_decide']:
  assert not re.search(r'(?m)^\s*(?:'+word+r')\b',p.read_text()),p
 rows.append(dict(module=p.stem,source_sha256=sha(p),receipt=str(q.relative_to(E)),object_sha256=sha(objects/(p.stem+'.olean')),exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps'],source_revision=r['source_revision'],print_axioms=r['print_axioms']))
(E/'proofs/manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',checked_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=rows),indent=2)+'\n');print('validated',len(rows),'focused modules and their current import hashes')
