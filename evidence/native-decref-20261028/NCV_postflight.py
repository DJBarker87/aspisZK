from pathlib import Path
import subprocess,json,hashlib,re,sys
import NCV_transport as t
E=t.E
entries=subprocess.check_output(['git','ls-tree','-r',t.REV,'crates','programs'],text=True).splitlines()
expected={line.split('\t',1)[1]:line.split()[2] for line in entries if line.split()[1]=='blob'}
last=json.loads((E/'NCV_K060/receipt.json').read_text())
modified={n.removeprefix('NCV_src/'):h for n,h in last['source_hashes'].items() if n in ['NCV_src/programs/r1-cost-probe/src/lib.rs','NCV_src/programs/r1-cost-probe/src/r1_pool_adapter.rs']}
for n in modified:
 text=(E/'NCV_K060/sources/NCV_src'/n).read_text()
 if n.endswith('r1_pool_adapter.rs'):
  text=''.join(l for l in text.splitlines(True) if not l.startswith('#[cfg_attr(kani, kani::'))
  text=text.replace('\n#[cfg(kani)] #[path="NCV_native.rs"] mod NCV_native;\n','')
 else:
  text=text.replace('#![cfg_attr(kani, feature(allocator_api))]\n#[cfg(kani)] extern crate alloc;\n','')
  text=text.replace('\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NCV_KMX;\n#[cfg(kani)] mod NCV_reference;\n','')
 original=subprocess.check_output(['git','show',t.REV+':'+n],text=True)
 assert text==original,('non-cfg source change',n)
# Admission before own script/config upload. Hashing and copying objects are inspection,
# not Lean/Rust/Kani builds; no additional proof invocation is launched.
t.admit('NCV_POSTFLIGHT')
payload=dict(expected=expected,modified=modified,library=json.loads((E/'NCV_RESOLVED_LIBRARY_PINS.json').read_text())['selected_objects'],imports=json.loads((E/'NCV_SETUP_PINS.json').read_text())['cache_imports'])
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(BASE);s=b/'NCV_src';x=json.loads(PAYLOAD);bad=[];missing=[]
for n,h in x['expected'].items():
 p=s/n
 if not p.is_file():missing.append(n);continue
 data=p.read_bytes()
 if n in x['modified']:ok=hashlib.sha256(data).hexdigest()==x['modified'][n]
 else:ok=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\\0'+data).hexdigest()==h
 if not ok:bad.append(n)
libbad=[p for p,v in x['library'].items() if hashlib.sha256(Path(p).read_bytes()).hexdigest()!=v['sha256']]
cache=b.parent/'codex-cx-decref-cache-20261028';cachebad=[]
for p,v in x['imports'].items():
 root=next(q for q in Path(p).parents if q.name in ['codex-cx-cpilot-cache-20261028','codex-cx-tx2codec-cache-20261028','codex-cx-leaf-cache-20261027'])
 q=cache/Path(p).relative_to(root)
 if hashlib.sha256(q.read_bytes()).hexdigest()!=v['selected_sha256']:cachebad.append(str(q))
assert not bad and not missing and not libbad and not cachebad,(bad,missing,libbad,cachebad)
objects={}
for p in (b/'NCV_objects').rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(b/'NCV_objects');q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True);data=p.read_bytes();h=hashlib.sha256(data).hexdigest()
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,str(q)
 else:q.write_bytes(data)
 objects[str(q)]={'sha256':h,'bytes':len(data)}
# Preserve sources, receipts and the owned cache. Remove only rebuildable owned
# compiler/solver scratch, after evidence and cache retention are confirmed.
removed=[]
for name in ['NCV_target','NCV_ref_target','NCV_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
out=dict(frozen_paths=len(x['expected']),cfg_only_modified_paths=list(x['modified']),source_errors=bad,missing=missing,library_errors=libbad,cache_errors=cachebad,retained_cache=str(cache),retained_objects=objects,removed=removed)
(b/'NCV_POSTFLIGHT.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out))
'''.replace('BASE',repr(t.B)).replace('PAYLOAD',repr(json.dumps(payload)))
r=t.py(code);assert r.returncode==0,r.stdout+r.stderr
(E/'NCV_POSTFLIGHT.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('postflight: frozen source/library/cache unchanged; owned compiler scratch removed')
