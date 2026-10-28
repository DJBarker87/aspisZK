from pathlib import Path
import json,hashlib,subprocess
import NDB_transport as t
E=t.E
t.admit('NDB_POSTFLIGHT')
rows=[json.loads(l) for l in (E/'NDB_ATTEMPTS.jsonl').read_text().splitlines()]
mods=sorted({r['module'] for r in rows if r['kind']=='lean' and r['exit_status']==0})
pins=json.loads((E/'NDB_SETUP_PINS.json').read_text())
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(BASE);s=b/'NDB_src';c=b.parent/'codex-cx-decref-cache-20261028'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=[b/'NDB_objects',c,b.parent/'codex-cx-sound-int2-20261025',b.parent/'codex-cx-sound-int2-20261025/objects']
lib={}
for suffix in ['Aeneas.olean']+[str(p.relative_to(Path(LIBROOT))) for p in Path(LIBROOT).joinpath('Aeneas').rglob('*.olean')]:
 p=next(root/suffix for root in roots if (root/suffix).is_file());lib[str(p)]=h(p)
old=PINS
library_match=all(h(Path(p))==v for p,v in old['library'].items())
imports_match=all(Path(p).exists() and h(Path(p))==v['sha256'] for p,v in old['cache_imports'].items())
objects={}
for name in MODS:
 p=b/'NDB_objects'/(name+'.olean');q=c/(name+'.olean')
 assert p.is_file(),name
 if q.exists():assert h(q)==h(p),'NEVER rewrite existing shared object'
 else:shutil.copyfile(p,q)
 assert h(q)==h(p),'new object copy mismatch'
 objects[name]=dict(path=str(q),sha256=h(q),size=q.stat().st_size)
files={str(p.relative_to(s)):h(p) for p in s.rglob('*') if p.is_file() and 'target' not in p.parts}
normal={}
p='programs/r1-cost-probe/src/r1_pool_adapter.rs'
x=(s/p).read_text();suffix='\\n#[cfg(kani)] #[path="NDB_native.rs"] mod NDB_native;\\n';assert x.endswith(suffix);normal[p]=hashlib.sha256(x[:-len(suffix)].encode()).hexdigest()
p='programs/r1-cost-probe/src/lib.rs';x=(s/p).read_text();prefix='#![cfg_attr(kani, feature(allocator_api))]\\n#[cfg(kani)] extern crate alloc;\\n';assert x.count(prefix)==1;x=x.replace(prefix,'',1)
suffix='\\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NDB_KMX;\\n#[cfg(kani)] mod NDB_reference;\\n';assert x.endswith(suffix);normal[p]=hashlib.sha256(x[:-len(suffix)].encode()).hexdigest()
assert library_match and imports_match
# Own rebuildable scratch only; retain the shared cache and frozen sources.
removed=[]
for name in ['NDB_target','NDB_tmp','NDB_objects']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
print(json.dumps(dict(resolved_aeneas=lib,original_library_unchanged=library_match,imported_cache_unchanged=imports_match,retained_objects=objects,source_hashes=files,normalized_frozen_files=normal,removed_owned_scratch=removed)))
'''.replace('BASE',repr(t.B)).replace('LIBROOT',repr('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')).replace('PINS',repr(pins)).replace('MODS',repr(mods))
r=t.py(code);assert r.returncode==0,r.stdout+r.stderr
x=json.loads(r.stdout)
for p,h in x['normalized_frozen_files'].items():assert hashlib.sha256(subprocess.check_output(['git','show',t.REV+':'+p])).hexdigest()==h
x['all_selected_modifications_cfg_kani_only']=True
x['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
x['native_reference_sha256']=hashlib.sha256(Path('evidence/native-decref-20261028/NCV_reference.rs').read_bytes()).hexdigest()
assert x['source_hashes']['programs/r1-cost-probe/src/NDB_reference.rs']==x['native_reference_sha256']
(E/'NDB_POSTFLIGHT.json').write_text(json.dumps(x,indent=2)+'\n')
print('postflight:',len(x['retained_objects']),'objects retained,',len(x['resolved_aeneas']),'Aeneas objects pinned')
