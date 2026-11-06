"""Pool duplicate SOURCE snapshots; retain every input and checksum losslessly."""
from pathlib import Path
import json,lzma,hashlib,sys
sys.dont_write_bytecode=True
import NKB_resolve
E=Path(__file__).resolve().parent;index=E/'NKB_POOLED_INPUTS.json';refs=json.loads(index.read_text()) if index.exists() else {};pool=E/'NKB_inputs';pool.mkdir(exist_ok=True)
immutable=['NKB_FROZEN_PAYLOAD.json.xz','NKB_FROZEN_PAYLOAD.json.sha256','NKB_STAGING_MANIFEST.json','NKB_KMX.patch','NKB_SUPPLEMENT.json']
fixed={hashlib.sha256((E/n).read_bytes()).hexdigest():n for n in immutable}
removed=[]
for line in (E/'NKB_ATTEMPTS.jsonl').read_text().splitlines():
 a=json.loads(line)['attempt'];receipt=json.loads((E/a/'receipt.json').read_text())
 for name,expected in receipt.get('source_hashes',{}).items():
  logical=a+'/sources/'+name;data=NKB_resolve.read(logical);sha=hashlib.sha256(data).hexdigest();assert sha==expected,logical
  entry=dict(sha256=sha,bytes=len(data))
  if sha in fixed:entry['file']=fixed[sha]
  else:
   q=pool/(sha+'.xz')
   if q.exists():assert lzma.decompress(q.read_bytes())==data
   else:q.write_bytes(lzma.compress(data,preset=6))
   entry['pool']=str(q.relative_to(E))
  refs[logical]=entry
  p=E/logical
  for q in [p,p.with_name(p.name+'.xz'),p.with_name(p.name+'.sha256')]:
   if q.is_file():removed.append(q)
# Commit the complete index BEFORE unlinking owned duplicate snapshots.
index.write_text(json.dumps(refs,indent=2,sort_keys=True)+'\n')
for p in set(removed):p.unlink()
for name in refs:NKB_resolve.read(name)
print('NKB lossless input pool: '+str(len(refs))+' source snapshots, frozen payload retained once')
