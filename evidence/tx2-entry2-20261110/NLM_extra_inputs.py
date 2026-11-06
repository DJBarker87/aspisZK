"""Complete frozen path dependencies omitted by the predecessor's file archive."""
from NLM_transport import *
import posixpath,tomllib,lzma,base64,hashlib
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
get=lambda n:subprocess.check_output(['git','show',rev+':'+n])
seen=set();todo=['Cargo.toml'];roots=['tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);d=tomllib.loads(get(n).decode());root=posixpath.dirname(n)
 if root:roots.append(root)
 for p in d.get('workspace',{}).get('members',[]):todo.append(posixpath.normpath(posixpath.join(root,p,'Cargo.toml')))
 def walk(v):
  if isinstance(v,dict):
   if 'path' in v and isinstance(v['path'],str) and ('version' in v or 'package' in v or 'optional' in v or 'default-features' in v or 'features' in v or v['path'].endswith(('crates/aspis-core','crates/aspis-prover','crates/aspis-statement'))):
    p=posixpath.normpath(posixpath.join(root,v['path'],'Cargo.toml'))
    if not v['path'].endswith('.rs'):todo.append(p)
   for x in v.values():walk(x)
  elif isinstance(v,list):
   for x in v:walk(x)
 # dependency maps have path-only entries too.
 def deps(v):
  if not isinstance(v,dict):return
  for k,z in v.items():
   if k in ['dependencies','dev-dependencies','build-dependencies'] and isinstance(z,dict):
    for dep in z.values():
     if isinstance(dep,dict) and isinstance(dep.get('path'),str):todo.append(posixpath.normpath(posixpath.join(root,dep['path'],'Cargo.toml')))
   elif isinstance(z,dict):deps(z)
 deps(d)
base=json.loads(lzma.decompress((E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz').read_bytes()))
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'--',*sorted(set(roots))],text=True).splitlines()
extra={}
for n in paths:
 if 'NLF_src/'+n in base:continue
 if '/target/' in n or n.endswith(('.olean','.elf')):continue
 raw=get(n);assert len(raw)<=20_000_000,n
 extra[n]=dict(data=base64.b64encode(raw).decode(),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
raw=json.dumps(extra,sort_keys=True).encode();compressed=lzma.compress(raw,preset=6)
(E/'NLM_NATIVE_EXTRA_INPUTS.json.xz').write_bytes(compressed);(E/'NLM_NATIVE_EXTRA_INPUTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
import sys
admission(sys.argv[1] if len(sys.argv)>1 else 'NLM_S003')
r=ssh('python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r});x=json.loads(lzma.decompress(base64.b64decode({base64.b64encode(compressed).decode()!r})));pins={{}}
for n,v in x.items():
 p=b/'NLM_src'/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(v['data']);assert hashlib.sha256(raw).hexdigest()==v['sha256']
 if p.exists():assert p.read_bytes()==raw,('frozen extra collision',n)
 else:p.write_bytes(raw)
 pins[n]=v['sha256']
(b/'NLM_EXTRA_PINS.json').write_text(json.dumps(pins,indent=1));print(json.dumps(dict(files=len(x),bytes=sum(v['bytes'] for v in x.values()))))
''');assert r.returncode==0,r.stderr
(E/'NLM_NATIVE_EXTRA_PINS.json').write_text(json.dumps({n:{k:v for k,v in z.items() if k!='data'} for n,z in extra.items()},indent=1))
print(r.stdout.strip())
