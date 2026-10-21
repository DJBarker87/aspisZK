#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'docs/research/100bit-spend-path-20261013/evidence/r4-transport2-20261021'
P=R/'docs/research/100bit-spend-path-20261013/lean-candidates/post25-indexed-addsmall-source-model-20261020'
M=json.loads((P/'worker-manifest.json').read_text())
O=Path('/tmp/codex-cx-r4-transport2-add-reference-objects');rows=[]
for r in M['proof_modules']:
 dest=O/(r['module'].replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q','dombarker@100.108.41.90:'+r['native_object_path'],str(dest)],check=True)
 h=hashlib.sha256(dest.read_bytes()).hexdigest();assert h==r['native_object_sha256']
 rows.append(dict(module=r['module'],path=str(dest),sha256=h,remote=r['native_object_path'],source=r['source'],source_sha256=r['source_sha256']))
(E/'add-reference-objects.json').write_text(json.dumps(rows,indent=2)+'\n')
