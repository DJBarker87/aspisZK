#!/usr/bin/env python3
"""Hash-pinned frozen diagnostics; never ship compiler outputs or task keys."""
import hashlib,json,shutil
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory3-20261021')
F=H.parent/'codex-cx-s10-inventory-20261021'
O=H/'packet';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p):return dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def dump(p,x):
 raw=(json.dumps(x,indent=2,sort_keys=True)+'\n').encode();assert len(raw)<=5_000_000;p.write_bytes(raw)
source=json.loads((F/'frozen-source-hashes.json').read_text())
assert all(sha(H/'src'/r['path'])==r['sha256'] for r in source['files'])
manifest=dict(schema='s10-frozen-diagnostics-v1',frozen_source_revision=source['source_revision'],source_files_rehashed=len(source['files']),source_manifest=pin(F/'frozen-source-hashes.json'),builds=[])
for d in sorted(H.glob('build-*-v*')):
 if not (d/'receipt/receipt.json').exists():continue
 out=O/d.name;out.mkdir(exist_ok=True)
 for p in (d/'receipt').iterdir():shutil.copy2(p,out/p.name)
 for p in [d/'command.json',d/'reservation.json',d/'artifact-comparison.json']:
  if p.exists():shutil.copy2(p,out/p.name)
 artifacts=[]
 for p in sorted(d.glob('compiler-output/*'))+sorted(d.glob('diagnostics/*')):
  if not p.is_file():continue
  artifacts.append(dict(**pin(p),generator='tools/s10-inventory3-20261021/rustc-diagnostics.py',retention='HOST ONLY: compiler output; pin and generator retained'))
  if p.suffix in ('.txt','.json'):shutil.copy2(p,out/p.name)
 manifest['builds'].append(dict(name=d.name,receipt=pin(d/'receipt/receipt.json'),artifacts=artifacts,comparison=json.loads((d/'artifact-comparison.json').read_text()) if (d/'artifact-comparison.json').exists() else None))
dump(O/'build-manifest.json',manifest)
print(json.dumps(dict(builds=len(manifest['builds']),source_files=manifest['source_files_rehashed'])))
