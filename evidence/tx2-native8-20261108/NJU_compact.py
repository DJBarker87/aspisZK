"""Losslessly deduplicate own pinned input capsules and compress own raw logs."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent
assert not (E/'NJU_CLIENT_ACTIVE').exists(),'Never compact an active attempt'
sha=lambda b:hashlib.sha256(b).hexdigest()
canon={}
for p in sorted(E.iterdir()):
 if p.is_file() and p.name.startswith('NJU_') and p.suffix not in ['.xz','.log']:
  canon.setdefault(sha(p.read_bytes()),str(p.relative_to(E)))
D=E/'NJU_INPUTS';D.mkdir(exist_ok=True);index={};total=0
for capsule in sorted(E.glob('NJU_[LK]*/sources')):
 receipt=json.loads((capsule.parent/'receipt.json').read_text())
 for p in sorted(capsule.rglob('*')):
  if not p.is_file():continue
  b=p.read_bytes();h=sha(b);n=str(p.relative_to(capsule));assert receipt['source_hashes'].get(n)==h,(p,n)
  if h in canon:target=canon[h];compressed=False
  else:
   target='NJU_INPUTS/'+h+'.xz';q=E/target
   if q.exists():assert lzma.decompress(q.read_bytes())==b
   else:q.write_bytes(lzma.compress(b,preset=6))
   canon[h]=target;compressed=True
  # A prior archived canonical entry is itself compressed.
  compressed=target.startswith('NJU_INPUTS/')
  index[str(p.relative_to(E))]=dict(sha256=h,bytes=len(b),retained=target,compressed=compressed)
  total+=len(b);p.unlink()
 for p in sorted(capsule.rglob('*'),key=lambda x:len(x.parts),reverse=True):
  if p.is_dir():p.rmdir()
 capsule.rmdir()
(E/'NJU_INPUT_INDEX.json').write_text(json.dumps(index,indent=1)+'\n')
logs=0
for p in sorted(E.rglob('*.log')):
 b=p.read_bytes();q=Path(str(p)+'.xz');z=lzma.compress(b,preset=6)
 if q.exists():assert lzma.decompress(q.read_bytes())==b
 else:q.write_bytes(z)
 Path(str(p)+'.sha256').write_text(sha(b)+'\n');p.unlink();logs+=1
from NJU_read import read_bytes
for name,r in index.items():assert sha(read_bytes(E/name))==r['sha256']
for p in E.rglob('*.log.xz'):read_bytes(Path(str(p)[:-3]))
(E/'NJU_COMPACTION.json').write_text(json.dumps(dict(source_capsules=len(index),capsule_raw_bytes=total,compressed_logs=logs,all_logical_inputs_hash_verified=True,lossless=True),indent=2)+'\n')
print(json.dumps(dict(source_capsules=len(index),compressed_logs=logs,verified=True)))
