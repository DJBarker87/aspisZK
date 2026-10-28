from pathlib import Path
import subprocess,json,hashlib
import NCX_transport as t
E=t.E
sha=lambda b:hashlib.sha256(b).hexdigest()
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',t.REV,'--','Cargo.toml','Cargo.lock','crates','programs'],text=True).splitlines()
frozen={p:sha(subprocess.check_output(['git','show',t.REV+':'+p])) for p in paths}
last=json.loads((E/'NCX_K040/receipt.json').read_text())['source_hashes']
initial=json.loads((E/'NCX_SETUP_PINS.json').read_text())
modules=[p[len('lean/'):len(p)-len('.lean')] for p in json.loads((E/'NCX_VALIDATION.json').read_text())['current_modules']]
t.admit('NCX_POSTFLIGHT')
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(B);cache=b.parent/'codex-cx-decref-cache-20261028';coherent=b.parent/'codex-cx-sound-int2-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source={};changed=[]
for name,h in FROZEN.items():
 p=b/'NCX_src'/name;actual=sha(p)
 if actual!=h:
  assert LAST.get('NCX_src/'+name)==actual,(name,'unexpected source change')
  changed.append(name)
 source[name]=dict(frozen_sha256=h,actual_sha256=actual)
assert set(changed)=={'crates/aspis-statement/src/lib.rs','crates/aspis-statement/src/pool_v1/verifier_registry.rs','programs/r1-cost-probe/src/lib.rs'},changed
# Strip only the exact cfg(kani) additions; the release body bytes must match.
for name in changed:
 p=b/'NCX_src'/name;s=p.read_text()
 if name=='crates/aspis-statement/src/lib.rs':
  s=s.removesuffix('\\n#[cfg(kani)] pub mod NCX_reference;\\n#[cfg(kani)] pub mod NCX_native;\\n')
 elif name.endswith('verifier_registry.rs'):
  s=''.join(line for line in s.splitlines(True) if not line.startswith('#[cfg_attr(kani,kani::'))
  s=s.removesuffix('\\n#[cfg(kani)] pub fn NCX_zero_native(value:&[u8;32])->bool {required_binding_is_zero(value)}\\n')
 else:
  s=s.replace('#![cfg_attr(kani, feature(allocator_api))]\\n#[cfg(kani)] extern crate alloc;\\n','',1)
  s=s.removesuffix('\\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NCX_KMX;\\n#[cfg(kani)] mod NCX_native;\\n')
 assert hashlib.sha256(s.encode()).hexdigest()==FROZEN[name],(name,'cfg stripping mismatch')
for name,h in INITIAL['cache'].items():assert sha(cache/name)==h,('imported cache changed',name)
roots=[b/'NCX_objects',cache,coherent,coherent/'objects'];resolved={}
for original,h in INITIAL['library'].items():
 rel=Path(original).relative_to(coherent/'objects')
 selected=next(p/rel for p in roots if (p/rel).is_file())
 assert sha(selected)==h,('resolved library drift',str(selected))
 resolved[str(selected)]=h
copied={}
for module in MODULES:
 stem=b/'NCX_objects'/module
 for p in stem.parent.glob(stem.name+'.*'):
  if not p.is_file():continue
  rel=p.relative_to(b/'NCX_objects');q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True)
  h=sha(p)
  if q.exists():assert sha(q)==h,('own cache collision',str(q))
  else:shutil.copy2(p,q)
  assert sha(q)==h
  copied[str(rel)]=dict(sha256=h,size=q.stat().st_size)
 assert (cache/(module+'.olean')).is_file(),module
pinned_tools={}
for p in [Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake')]:pinned_tools[str(p)]=dict(sha256=sha(p),size=p.stat().st_size)
# Only rebuildable own output dirs, after every canonical object is retained.
cleanup={}
for name in ['NCX_target','NCX_ref_target','NCX_objects','NCX_tmp']:
 p=b/name
 files=[f for f in p.rglob('*') if f.is_file()] if p.exists() else []
 cleanup[name]=dict(files=len(files),bytes=sum(f.stat().st_size for f in files))
 if p.exists():shutil.rmtree(p)
assert cache.is_dir()
print(json.dumps(dict(source_files=source,cfg_only_parents=changed,imported_cache_files_retained=len(INITIAL['cache']),resolved_aeneas_objects=resolved,canonical_objects_retained=copied,tool_pins=pinned_tools,cleanup=cleanup,retained_cache=str(cache))))
'''.replace('INITIAL',repr(initial)).replace('FROZEN',repr(frozen)).replace('LAST',repr(last)).replace('MODULES',repr(modules)).replace('B',repr(t.B),1)
r=t.py(code);assert r.returncode==0,r.stdout+r.stderr
(E/'NCX_POSTFLIGHT.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('postflight source, imported caches, library and retained objects verified; own scratch cleaned')
