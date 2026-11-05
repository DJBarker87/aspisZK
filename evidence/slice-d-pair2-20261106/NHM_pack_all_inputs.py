"""Lossless content-addressed archival of every receipt source input, once by SHA."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;pool=E/'NHM_INPUTS_BY_SHA256';known={};removed=0
for p in E.glob('NHM_[KLE][0-9][0-9][0-9]/SOURCE_INDEX.json'):
 for r in json.loads(p.read_text()).values():known[r['sha256']]=r
for receipt in sorted(E.glob('NHM_[KLE][0-9][0-9][0-9]/receipt.json')):
 a=receipt.parent;r=json.loads(receipt.read_text());idx=a/'SOURCE_INDEX.json'
 if idx.exists():continue
 rows={}
 for p in sorted((a/'sources').rglob('*')):
  if not p.is_file():continue
  name=str(p.relative_to(a/'sources'));data=p.read_bytes();h=hashlib.sha256(data).hexdigest();assert r['source_hashes'][name]==h
  if h not in known:
   dest=pool/(h+'.xz');dest.parent.mkdir(exist_ok=True)
   if not dest.exists():dest.write_bytes(lzma.compress(data,preset=6))
   assert hashlib.sha256(lzma.decompress(dest.read_bytes())).hexdigest()==h
   known[h]=dict(sha256=h,bytes=len(data),payload=str(dest.relative_to(E)))
  rows[name]=known[h];p.unlink();removed+=len(data)
 idx.write_text(json.dumps(rows,indent=2)+'\n')
 for p in sorted((a/'sources').rglob('*'),key=lambda p:len(p.parts),reverse=True):
  if p.is_dir():p.rmdir()
 if (a/'sources').exists():(a/'sources').rmdir()
(E/'NHM_ALL_SHARED_INPUTS.json').write_text(json.dumps(dict(unique_inputs=len(known),unique_uncompressed_bytes=sum(r['bytes']for r in known.values()),method='source_hashes -> SOURCE_INDEX.json -> one shared SHA-addressed xz payload; every input retained',inputs=known),indent=2)+'\n')
print(json.dumps(dict(unique=len(known),uncompressed=sum(r['bytes']for r in known.values()),source_bytes_deduplicated=removed)))
