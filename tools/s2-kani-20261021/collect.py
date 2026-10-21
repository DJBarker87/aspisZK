#!/usr/bin/env python3
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2-kani-20261021'
rows=[]
for p in sorted((E/'host-receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());name=p.parent.name;r.update(attempt=name,receipt=str(p.relative_to(R)))
 inp=E/'host'/(name+'-inputs.json')
 if inp.exists():
  inputs=json.loads(inp.read_text());r['source_sha256']=inputs['source_sha256'];deps=inputs['source_cut']['sources'];r['inputs']=str(inp.relative_to(R));r['deps_fingerprint']=hashlib.sha256(json.dumps(dict(sources=deps,tools=json.loads((E/'kani-tools.json').read_text())),sort_keys=True).encode()).hexdigest()
 else:
  cone='header' if name.startswith('header-') else 'parser'
  # Extraction references never changed during these extraction attempts.
  inp=E/(cone+'-extraction')/(('charon' if 'charon' in name else 'aeneas')+'-input.json')
  inputs=json.loads(inp.read_text());r['source_sha256']=inputs['source_sha256'];r['inputs']=str(inp.relative_to(R));r['deps_fingerprint']=hashlib.sha256(json.dumps(dict(tools=inputs['tools'],env=inputs['environment']),sort_keys=True).encode()).hexdigest()
 r['status']='accepted' if r['exit_status']==0 else ('deliberately stopped: dynamic trace explosion; replaced by fixed array' if name=='callers-v2' else 'failed')
 rows.append(r)
(E/'host-manifest.json').write_text(json.dumps({'schema':'s2-kani-host-v1','attempts':rows},indent=2)+'\n')
