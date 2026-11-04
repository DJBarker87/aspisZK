"""Content-address repeated receipt input snapshots; preserve every original byte."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;blob=E/'NGO_blobs';blob.mkdir(exist_ok=True)
entries=[]
for directory in sorted(E.glob('NGO_*/sources')):
 for p in sorted(directory.rglob('*')):
  if not p.is_file()or p.name.endswith('.REFERENCE.json'):continue
  data=p.read_bytes();digest=hashlib.sha256(data).hexdigest();dest=blob/(digest+'.source.xz');check=blob/(digest+'.source.sha256')
  if dest.exists():assert lzma.decompress(dest.read_bytes())==data
  else:dest.write_bytes(lzma.compress(data,preset=6));check.write_text(digest+'\n')
  row=dict(original=str(p.relative_to(E)),sha256=digest,bytes=len(data),blob=str(dest.relative_to(E)))
  ref=Path(str(p)+'.REFERENCE.json');ref.write_text(json.dumps(row,indent=1));p.unlink();entries.append(row)
old=E/'NGO_PACK.json'
if old.exists():entries=json.loads(old.read_text())['entries']+entries
old.write_text(json.dumps(dict(entries=entries,claim='Every receipt source input remains recoverable byte-for-byte; this is storage deduplication, not exclusion'),indent=1))
print(json.dumps(dict(snapshots=len(entries),unique_source_blobs=len(list(blob.glob('*.xz'))),uncompressed_bytes=sum(x['bytes']for x in entries),compressed_bytes=sum(p.stat().st_size for p in blob.glob('*.xz')))))
