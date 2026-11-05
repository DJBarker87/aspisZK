"""Lossless SHA-addressed storage for immutable completed-attempt source inputs."""
from pathlib import Path
import json,hashlib,os,re
E=Path(__file__).resolve().parent;D=E/'NIL_inputs';D.mkdir(exist_ok=True)
records=[]
for receipt in sorted(E.glob('NIL_[KLE][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(receipt.read_text())
 for name,pin in r['source_hashes'].items():
  p=receipt.parent/'sources'/name
  raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();assert h==pin,(p,h,pin)
  if len(raw)<4096:continue
  q=D/(h+'.txt')
  if q.exists():assert q.read_bytes()==raw
  else:q.write_bytes(raw)
  if not p.is_symlink():p.unlink();p.symlink_to(os.path.relpath(q,p.parent))
  assert p.read_bytes()==raw
  records.append({'path':str(p.relative_to(E)),'input':str(q.relative_to(E)),'sha256':h,'bytes':len(raw)})
(E/'NIL_SOURCE_ARCHIVE.json').write_text(json.dumps({'policy':'only immutable completed scope inputs; every original path resolves byte-identically','records':records,'unique_bytes':sum(p.stat().st_size for p in D.iterdir() if p.is_file())},indent=2)+'\n')
print(json.dumps({'references':len(records),'unique_bytes':sum(p.stat().st_size for p in D.iterdir() if p.is_file())}))
