"""Hash the independent final cohort; never repairs or substitutes shared objects."""
from pathlib import Path
import json,hashlib,lzma,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2e-20261029');plan=json.loads((D/'frozen-proof-manifest.json').read_text());env=json.loads((D/'env-J.json').read_text());roots=list(map(Path,env['LEAN_PATH'].split(':')))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def find(m):
 rel=m.replace('.','/')+'.olean';return next((r/rel for r in roots if(r/rel).exists()),None)
ext=[]
for r in json.loads((D/'external.json').read_text()):
 m=r['module'].replace('/','.');p=find(m);h=sha(p)if p else None;ext.append(dict(module=m,path=str(p),expected=r['object_sha256'],actual=h,ok=h==r['object_sha256']))
objects=[]
for m,r in plan['modules'].items():
 s=D/'lean-sources'/(m.replace('.','/')+'.lean');o=find(m);assert s.exists()and o,m
 assert sha(s)==r['source_sha256'],m
 imports=[]
 for imp in r['imports']:
  p=find(imp);assert p,imp
  assert not imp.startswith('AspisR72Sampler'),(m,imp)
  imports.append(dict(module=imp,path=str(p),object_sha256=sha(p)))
 objects.append(dict(module=m,source_sha256=sha(s),source_blob=r['source_blob'],object_sha256=sha(o),object_bytes=o.stat().st_size,path=str(o),imports=imports))
assert all(r['ok']for r in ext)
feature_artifacts=[]
for p in (D/'target/release/.fingerprint').glob('*/bin-associations.json'):
 r=json.loads(p.read_text());feature_artifacts.append(dict(path=str(p),sha256=sha(p),rustflags=r.get('rustflags'),profile=r.get('profile'),features=r.get('features')))
native=[]
for r in json.loads((D/'native-source-pins.json').read_text()):
 p=D.parent/'codex-pv-fscan-20261028/src'/r['path'];h=sha(p)if p.exists()else None;native.append(dict(**r,actual=h,ok=h==r['sha256'],host_path=str(p)))
assert all(r['ok']for r in native)
registry=[]
for r in json.loads((D/'source-paths.json').read_text()):
 p=Path(r['path']);h=sha(p)if p.exists()else None;registry.append(dict(**r,actual=h,ok=h==r['sha256']))
assert all(r['ok']for r in registry)
sent=D.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt';collisions=[line for line in sent.read_text().splitlines()if re.search(r'\b622\d\d\b',line)] if sent.exists()else[];assert not collisions
binary=D/'target/release/associations'
r=dict(scope='independent SHA and logical pointer/from_fn cohort only; sampler cone explicitly excluded under h6',objects=objects,external=ext,env=env,native_source_checks=native,registry_source_checks=registry,rust_codegen_artifacts=feature_artifacts,native_binary=dict(path=str(binary),sha256=sha(binary),bytes=binary.stat().st_size),shared_sent_collisions=collisions,sampler_cohort_stop=json.loads((D/'sampler-cohort-stop.json').read_text()),private_cache_reuse=False,source_revision=plan['revision'])
raw=json.dumps(r,indent=2).encode();(D/'dependency-fingerprint.json.xz').write_bytes(lzma.compress(raw,preset=6));(D/'dependency-fingerprint.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(owned=len(objects),external=len(ext),native=len(native),registry=len(registry),rust_codegen_artifacts=feature_artifacts,source_pins_match=True,sampler_excluded=True)),flush=True)
