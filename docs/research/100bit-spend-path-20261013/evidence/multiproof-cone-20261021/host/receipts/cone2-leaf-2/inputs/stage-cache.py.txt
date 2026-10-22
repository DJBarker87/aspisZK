#!/usr/bin/env python3
"""Private additive namespace union, with immutable source hashes; no builds."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/multiproof-cone-20261021'
O=Path('/tmp/codex-cx-multiproof-cone-20261021-objects')
record=E/'cache-overlay.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
data=json.loads(record.read_text()) if record.exists() else dict(reason='Task-private cache namespace union for specifically diagnosed missing legacy decoder imports; no shared object is built or replaced. Focused cache evidence is not a coherent release replay.',objects=[])
paths=json.loads((E/'MultiproofConeEndian-1/command.json').read_text())['lean_path'].split(':')
paths+=['/tmp/r1-circle-pointwise-nucclosure-local-v4b/objects']
existing={row['target'] for row in data['objects']}
for name in ['AspisV8R19','AspisR72Sampler']:
 selected={}
 for base in paths:
  if not base or Path(base)==O:continue
  namespace=Path(base)/name
  if not namespace.is_dir():continue
  for obj in sorted(namespace.rglob('*.olean')):
   rel=obj.relative_to(namespace)
   if rel not in selected:selected[rel]=obj
 for rel,obj in sorted(selected.items()):
  target=O/name/rel
  for src,dst in [(obj,target)]+[(Path(str(obj)+suffix),Path(str(target)+suffix)) for suffix in ['.server','.private']]+[(obj.with_suffix('.ir'),target.with_suffix('.ir'))]:
   if src.exists() and str(dst) not in existing:
    data['objects'].append(dict(source=str(src),target=str(dst),sha256=sha(src),bytes=src.stat().st_size));existing.add(str(dst))
record.write_text(json.dumps(data,indent=2)+'\n')
for row in data['objects']:
 src,dst=Path(row['source']),Path(row['target']);assert sha(src)==row['sha256'];assert src.stat().st_size==row['bytes']
 assert dst.is_relative_to(O)
 dst.parent.mkdir(parents=True,exist_ok=True)
 if not dst.exists():dst.symlink_to(src)
 assert dst.is_symlink() and dst.resolve()==src.resolve()
print('Validated private namespace objects/companions:',len(data['objects']))
