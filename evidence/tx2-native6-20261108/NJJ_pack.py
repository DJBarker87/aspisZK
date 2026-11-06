"""Lossless receipt input deduplication; no input is ignored or discarded."""
from pathlib import Path
import json,hashlib,lzma,shutil
E=Path(__file__).resolve().parent;store=E/'NJJ_inputs';store.mkdir(exist_ok=True)
p=E/'NJJ_INPUTS_INDEX.json';index=json.loads(p.read_text()) if p.exists() else {}
for root in sorted(E.glob('NJJ_[LKE][0-9][0-9][0-9]/sources')):
 for f in sorted(root.rglob('*')):
  if not f.is_file():continue
  data=f.read_bytes();h=hashlib.sha256(data).hexdigest();dest=store/(h+'.xz')
  if not dest.exists():dest.write_bytes(lzma.compress(data,preset=6))
  assert lzma.decompress(dest.read_bytes())==data
  index[str(f.relative_to(E))]=dict(sha256=h,bytes=len(data),archive=str(dest.relative_to(E)))
  f.unlink()
 shutil.rmtree(root)
p.write_text(json.dumps(index,indent=2)+'\n')
# Exact replay: archive entries expand to the original receipt snapshots.
for name,r in index.items():
 data=lzma.decompress((E/r['archive']).read_bytes());assert hashlib.sha256(data).hexdigest()==r['sha256'] and len(data)==r['bytes']
print(json.dumps(dict(verified_inputs=len(index),unique_blobs=len(list(store.glob('*.xz'))))))
