from pathlib import Path
import hashlib,json,struct
w=Path('/home/dombarker/project-offloads/prepared-source-powers-meaning-v2-20261020')
owners=json.loads((w/'local-cache-owner-inventory.json').read_text())
config=json.loads((w/'config.json').read_text());builtin=Path(config['lean']).parents[1]/'lib/lean'
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
queue=['PreparedSourcePowersBoundariesV1','CurrentPreparedCandidateSamplers'];seen={};missing=[]
while queue:
 n=queue.pop()
 if n in seen:continue
 rel=n.replace('.','/')+'.olean'
 path=Path(owners[rel]) if rel in owners else builtin/rel
 if not path.is_file():missing.append((n,str(path)));continue
 ds=imports(path)
 seen[n]={'path':str(path),'relative':rel,'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'builtin':rel not in owners,'imports':ds}
 queue+=ds
assert not missing,missing
(w/'local-cache-transitive-closure.json').write_text(json.dumps(seen,indent=2)+'\n')
print(json.dumps({'modules':len(seen),'non_builtin_modules':sum(not x['builtin'] for x in seen.values()),'non_builtin_bytes':sum(x['bytes'] for x in seen.values() if not x['builtin'])}))
cache=w/'local-cache-closure'
for n,row in seen.items():
 if row['builtin']:continue
 f=cache/row['relative'];f.parent.mkdir(parents=True,exist_ok=True)
 if not f.exists():f.symlink_to(row['path'])
 # Lean may also request the matching IR or split object parts. Copy cached artifacts only.
 for suffix in ['.ir','.olean.private','.olean.server']:
  original=Path(row['path']).with_suffix(suffix)
  target=f.with_suffix(suffix)
  if original.is_file() and not target.exists():target.symlink_to(original)
