#!/usr/bin/env python3
"""Complete missing namespace members in a new symlink-only warm overlay.
Existing cache roots are never modified; earlier source-owner choices win.
"""
from pathlib import Path
import hashlib,json,os
R=Path(__file__).resolve().parents[2]
base=Path('/tmp/s126-round-canonical-path-20261024.txt').read_text().strip().split(':')
circle=Path('/tmp/s126-circle-lean-path-20261024.txt').read_text().strip().split(':')
roots=list(dict.fromkeys(base+circle)); dest=Path('/tmp/s126-finish-namespace-union-20261024');dest.mkdir(exist_ok=True)
for stale in dest.rglob('*'):
 if stale.is_symlink() and not stale.exists():stale.unlink()
names=sorted({p.name for root in roots if Path(root).is_dir() for p in Path(root).iterdir() if p.is_dir() and p.name.startswith('Aspis')})
selected={}
for root in roots:
 for name in names:
  directory=Path(root)/name
  if not directory.is_dir():continue
  for parent,dirs,files in os.walk(directory,followlinks=True):
   for file in files:
    if not file.endswith(('.olean','.olean.private','.olean.server')):continue
    src=Path(parent)/file
    if not src.is_file():continue
    rel=src.relative_to(root); key=str(rel)
    if key in selected:continue
    p=dest/rel;p.parent.mkdir(parents=True,exist_ok=True)
    if not p.exists():p.symlink_to(src.resolve())
    assert p.resolve()==src.resolve(),p
    selected[key]=dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest())
    if file.endswith('.olean'):
     ir=src.resolve().with_suffix('.ir')
     if ir.is_file():
      irp=(dest/rel).with_suffix('.ir')
      if not irp.exists():irp.symlink_to(ir)
      assert irp.resolve()==ir.resolve(),irp
      selected[str(rel.with_suffix('.ir'))]=dict(source=str(ir),sha256=hashlib.sha256(ir.read_bytes()).hexdigest(),companion_of=key)

E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-finish-selectors-20261024'
Path('/tmp/s126-finish-namespace-cache-inventory-20261024.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',roots=roots,selected=selected,note='New symlink overlay only. Base owner precedence retained; missing circle dependency namespace members filled. Not a coherent rebuild or release theorem.'),indent=2)+'\n')
Path('/tmp/s126-finish-lean-path-20261024.txt').write_text(':'.join([str(dest),*roots])+'\n')
print(json.dumps(dict(namespace_cache_members=len(selected))))
