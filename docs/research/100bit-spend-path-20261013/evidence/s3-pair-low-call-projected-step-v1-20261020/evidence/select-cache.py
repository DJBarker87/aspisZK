from pathlib import Path
import hashlib,json,struct
roots=[Path('/tmp/s3-powers-v18-local-evidence/objects'),Path('/tmp/s3-pair-low-call-adapter-v1-local-20261020/objects'),Path('/tmp/s3-powers-v16-local-overlay'),Path('/tmp/s4-p6-formatter-repair-closure'),Path('/tmp/prepared-local-warm-cache-20261020')]
builtin=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
def imports(path):
 b=path.read_bytes();assert b[:5]==b'olean',str(path)
 base,root=struct.unpack_from('<QQ',b,80)
 def u(o):return struct.unpack_from('<Q',b,o)[0]
 def name(p):
  if p&1:assert p==1;return ''
  o=p-base;tag=b[o+7];prefix=name(u(o+8));assert tag in [1,2]
  if tag==1:
   q=u(o+16)-base;t=b[q+32:b.index(0,q+32)].decode()
  else:t=str(u(o+16))
  return prefix+'.'+t if prefix else t
 arr=u(root-base+8)-base
 return list(dict.fromkeys(name(u(u(arr+24+8*i)-base+8)) for i in range(u(arr+8))))
queue=['S3PairLowCallLowStepV1','S3PairLowCallOperationMapV1'];seen={};missing=[]
while queue:
 n=queue.pop()
 if n in seen:continue
 rel=n.replace('.','/')+'.olean'
 path=next((r/rel for r in roots+[builtin] if (r/rel).is_file()),None)
 if path is None:missing.append(n);continue
 ds=imports(path);seen[n]={'path':str(path),'relative':rel,'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'builtin':path.is_relative_to(builtin),'imports':ds};queue+=ds
print(json.dumps({'modules':len(seen),'missing':missing}))
assert not missing
out=Path('/tmp/root-s3-projected-cache-20261020');out.mkdir(exist_ok=True)
for row in seen.values():
 if row['builtin']:continue
 f=out/row['relative'];f.parent.mkdir(parents=True,exist_ok=True)
 if not f.exists():f.symlink_to(row['path'])
 for suffix in ['.ir','.olean.private','.olean.server']:
  original=Path(row['path']).with_suffix(suffix);target=f.with_suffix(suffix)
  if original.is_file() and not target.exists():target.symlink_to(original)
Path('/tmp/root-s3-projected-cache-closure.json').write_text(json.dumps(seen,indent=2)+'\n')
