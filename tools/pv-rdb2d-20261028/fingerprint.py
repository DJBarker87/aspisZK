from pathlib import Path
import json,hashlib,lzma,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');env=json.loads((D/'env-J.json').read_text());roots=list(map(Path,env['LEAN_PATH'].split(':')))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
external=[]
for r in json.loads((D/'external.json').read_text()):
 rel=r['module'].replace('.','/')+'.olean';p=next((root/rel for root in roots if(root/rel).exists()),None);h=sha(p)if p else None
 external.append(dict(module=r['module'],path=str(p),expected=r['object_sha256'],actual=h,ok=h==r['object_sha256']))
objects=[]
for r in json.loads((D/'rdb2d-frozen-proof-manifest.json').read_text())['modules']:
 m=r['module'];s=D/'lean-sources'/(m+'.lean');o=D/'lean-objects'/(m+'.olean');assert sha(s)==r['source_sha256'],m
 imports=[]
 for imp in re.findall(r'^import (\S+)',s.read_text(),re.M):
  rel=imp.replace('.','/')+'.olean';p=next((root/rel for root in roots if(root/rel).exists()),None);assert p,imp
  imports.append(dict(module=imp,path=str(p),object_sha256=sha(p)))
 objects.append(dict(**r,object_sha256=sha(o),object_bytes=o.stat().st_size,imports=imports))
old=json.loads(lzma.decompress((D/'final-dependency-fingerprint.json.xz').read_bytes()));ejr=[]
for r in old['canonical_ejr_objects']:
 rel=r['module'].replace('.','/')+'.olean';p=next((root/rel for root in roots if(root/rel).exists()),None);h=sha(p)if p else None
 ejr.append(dict(module=r['module'],source_sha256=r['source_sha256'],expected=r['object_sha256'],actual=h,ok=h==r['object_sha256'],path=str(p)))
result=dict(external=external,objects=objects,canonical_ejr=ejr,env=env,reuse='no old RDB2C private objects survived; four reserve dependencies and two canonical R72 modules rebuilt; EJR shared objects reused read-only after full fingerprint checks')
raw=json.dumps(result,indent=2).encode();(D/'rdb2d-dependency-fingerprint.json.xz').write_bytes(lzma.compress(raw,preset=6));(D/'rdb2d-dependency-fingerprint.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
assert all(r['ok']for r in external);assert all(r['ok']for r in ejr),[r for r in ejr if not r['ok']]
print(json.dumps(dict(external=len(external),owned=len(objects),canonical=len(ejr),ok=True)),flush=True)
