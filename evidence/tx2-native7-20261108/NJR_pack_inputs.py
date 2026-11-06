"""Lossless content-addressed storage for repeated captured inputs; never discard a failed input."""
from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
indexPath=E/'NJR_INPUT_INDEX.json'
index=json.loads(indexPath.read_text()) if indexPath.exists() else {}
objects=E/'NJR_INPUT_OBJECTS';objects.mkdir(exist_ok=True)
current={}
for p in sorted(E.rglob('*')):
 if not p.is_file() or any(re.fullmatch('NJR_[KL][0-9]{3}',s) for s in p.relative_to(E).parts) or 'NJR_INPUT_OBJECTS' in p.parts:continue
 if p.stat().st_size>20_000_000:raise RuntimeError(('over20MB',p))
 current.setdefault(sha(p.read_bytes()),str(p.relative_to(E)))
packed=0;rawbytes=0
for p in sorted(E.glob('NJR_[KL][0-9][0-9][0-9]/sources/**/*')):
 if not p.is_file():continue
 raw=p.read_bytes();h=sha(raw);rel=str(p.relative_to(E));row=dict(sha256=h,bytes=len(raw))
 if h in current:row['file']=current[h]
 else:
  q=objects/(h+'.xz')
  if not q.exists():q.write_bytes(lzma.compress(raw,preset=6))
  assert sha(lzma.decompress(q.read_bytes()))==h
  row['archive']=str(q.relative_to(E))
 if rel in index:assert row==index[rel]
 index[rel]=row;rawbytes+=len(raw);packed+=1
indexPath.write_text(json.dumps(index,sort_keys=True,indent=1)+'\n')
def resolve(row):
 raw=(E/row['file']).read_bytes() if 'file' in row else lzma.decompress((E/row['archive']).read_bytes())
 assert len(raw)==row['bytes'] and sha(raw)==row['sha256'];return raw
for row in index.values():resolve(row)
for p in E.glob('NJR_[KL][0-9][0-9][0-9]/receipt.json'):
 r=json.loads(p.read_text())
 for name,h in r['source_hashes'].items():
  rel=str((p.parent/'sources'/name).relative_to(E))
  assert rel in index,(r['attempt'],name)
  assert index[rel]['sha256']==h,(r['attempt'],name)
for p in sorted(E.glob('NJR_[KL][0-9][0-9][0-9]/sources/**/*'),reverse=True):
 if p.is_file():p.unlink()
 elif p.is_dir():p.rmdir()
for p in E.glob('NJR_[KL][0-9][0-9][0-9]/sources'):
 if not any(p.iterdir()):p.rmdir()
result=dict(captured_input_files=len(index),unique_archives=len(list(objects.glob('*.xz'))),archive_bytes=sum(p.stat().st_size for p in objects.glob('*.xz')),deduplicated_raw_bytes=sum(row["bytes"] for row in index.values()),receipt_source_hashes_verified=True,failed_inputs_retained=True)
(E/'NJR_INPUT_RETENTION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
