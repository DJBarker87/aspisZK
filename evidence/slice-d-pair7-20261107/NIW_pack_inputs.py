"""Deduplicate native receipt source snapshots once by content hash, losslessly."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;pool=E/'NIW_K001/inputs_by_sha256';pool.mkdir(parents=True,exist_ok=True)
index={};saved=0
for receipt in sorted(E.glob('NIW_K[0-9][0-9][0-9]/receipt.json')):
 a=receipt.parent;r=json.loads(receipt.read_text());rows={}
 if (a/'SOURCE_INDEX.json').exists():
  rows=json.loads((a/'SOURCE_INDEX.json').read_text())
  for row in rows.values():index[row['sha256']]=row['bytes']
  continue
 for p in sorted((a/'sources').rglob('*')):
  if not p.is_file():continue
  n=str(p.relative_to(a/'sources'));data=p.read_bytes();sha=hashlib.sha256(data).hexdigest()
  assert r['source_hashes'][n]==sha,(a.name,n)
  dest=pool/(sha+'.xz')
  if not dest.exists():dest.write_bytes(lzma.compress(data,preset=6))
  assert hashlib.sha256(lzma.decompress(dest.read_bytes())).hexdigest()==sha
  rows[n]=dict(sha256=sha,bytes=len(data),payload=str(dest.relative_to(E)))
  index[sha]=len(data);saved+=len(data);p.unlink()
 (a/'SOURCE_INDEX.json').write_text(json.dumps(rows,indent=2)+'\n')
 for p in sorted((a/'sources').rglob('*'),key=lambda p:len(p.parts),reverse=True):
  if p.is_dir():p.rmdir()
 if (a/'sources').exists():(a/'sources').rmdir()
(E/'NIW_SHARED_INPUTS.json').write_text(json.dumps(dict(unique_inputs=len(index),unique_uncompressed_bytes=sum(index.values()),payload_directory=str(pool.relative_to(E)),method='Exact per-attempt source_hashes -> SOURCE_INDEX.json -> shared xz payload, hash-checked; no evidence input omitted',sha256_sizes=index),indent=2)+'\n')
print(json.dumps(dict(unique=len(index),uncompressed=sum(index.values()),source_bytes_deduplicated=saved)))
