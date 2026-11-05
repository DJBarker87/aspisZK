"""Deduplicate evidence inputs without dropping bytes or modifying raw receipts."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent
canon={}
for p in E.iterdir():
 if p.is_file() and not p.name.endswith(('.xz','.sha256','.ref.json')) and p.name!='NGU_PACK.json' and not (p.name.startswith('NGU_K') and p.name.endswith('-all-crate-features.json')):
  canon.setdefault(hashlib.sha256(p.read_bytes()).hexdigest(),p)
store=E/'NGU_inputs';store.mkdir(exist_ok=True);rows=[]
files=[p for d in E.glob('NGU_[LKE][0-9][0-9][0-9]/sources') for p in d.rglob('*') if p.is_file() and not p.name.endswith('.ref.json')]
files+=list(E.glob('NGU_K*-all-crate-features.json'))
for p in sorted(files):
 b=p.read_bytes();h=hashlib.sha256(b).hexdigest();q=canon.get(h);encoding='identity'
 if q is None:
  q=store/(h+'.xz');z=lzma.compress(b,preset=6)
  if q.exists():assert q.read_bytes()==z
  else:q.write_bytes(z)
  canon[h]=q;encoding='xz'
 elif q.suffix=='.xz':encoding='xz'
 row=dict(target=str(q.relative_to(E)),sha256=h,bytes=len(b),encoding=encoding)
 Path(str(p)+'.ref.json').write_text(json.dumps(row,indent=1)+'\n');p.unlink()
 rows.append(dict(path=str(p.relative_to(E)),**row))
# Retain idempotent prior rows if the pack step is repeated after collection.
index=E/'NGU_PACK.json'
if index.exists():rows=json.loads(index.read_text())['references']+rows
unique={r['path']:r for r in rows}
index.write_text(json.dumps(dict(references=list(unique.values()),source_bytes=sum(r['bytes'] for r in unique.values()),retained_input_objects=len(list(store.glob('*.xz'))),policy='Every source/metadata input is retained once by content hash; .ref.json is a checked path/length/SHA256 reference, not an exclusion. NGU_io.py reconstructs exact bytes. Raw receipts and outcomes are not rewritten.'),indent=1)+'\n')
print(json.dumps(dict(references=len(unique),input_objects=len(list(store.glob('*.xz'))))))
