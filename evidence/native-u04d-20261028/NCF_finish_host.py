"""Read-only provenance audit, then remove only this job's rebuildable Rust output."""
from pathlib import Path
import importlib.util,sys,json,subprocess,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'native-u04c-20261028';sys.argv=['ncf','unused'];sp=importlib.util.spec_from_file_location('inherited',P/'NCC_native.py');m=importlib.util.module_from_spec(sp)
exec(compile((P/'NCC_native.py').read_text().replace('NCC_NATIVE_TRANSPORT','NCF_NATIVE_TRANSPORT'),str(P/'NCC_native.py'),'exec'),m.__dict__);m.E=E
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['crates/aspis-statement/src/pool_v1/format.rs','programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']
frozen={p:subprocess.check_output(['git','show',REV+':'+p],text=True) for p in paths}
blobs={l.split(' ',1)[1]:l.split(' ',1)[0] for l in subprocess.check_output(['git','ls-tree','-r','--format=%(objectname) %(path)',REV,'crates','programs','Cargo.toml','Cargo.lock'],text=True).splitlines()}
pins=json.loads((E/'NCF_L001-object-pins.json').read_text())
code=f'''from pathlib import Path
import hashlib,json,difflib,os,shutil
b=Path({m.B!r});s=b/'NBU_src';frozen={frozen!r};blobs={blobs!r};pins={pins!r}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(8*1024*1024),b''):h.update(block)
 return h.hexdigest()
assert all((b/('NCF_K%03d'%i)/'receipt.json').exists() for i in range(1,71))
assert json.loads((b/'NCF_BATCH68.json.status.json').read_text())['state']=='complete'
old={{}}
for name in ['crates/aspis-statement/src/lib.rs','crates/aspis-statement/src/pool_v1/verifier_registry.rs']:
 old[name]=(b/'NCC_K060/sources/NBU_src'/name).read_text()
old.update(frozen)
reg='crates/aspis-statement/src/pool_v1/verifier_registry.rs'
assert (s/reg).read_text().removesuffix('\\n#[cfg(kani)]\\n#[path = "NCF_slots.rs"]\\nmod NCF_slots;\\n')==old[reg]
lib='crates/aspis-statement/src/lib.rs'
assert (s/lib).read_text().removesuffix('\\n#[cfg(kani)]\\npub mod NCF_policy;\\n')==old[lib]
f='crates/aspis-statement/src/pool_v1/format.rs';assert ''.join(l for l in (s/f).read_text().splitlines(True) if '#[cfg_attr(kani, kani::' not in l)==old[f]
f='programs/r1-cost-probe/src/lib.rs';t=(s/f).read_text().removesuffix('\\n#[cfg(kani)]\\n#[path = "../../../KMX_stubs.rs"]\\nmod NCF_KMX;\\n');t=t.replace('#![cfg_attr(kani, feature(allocator_api))]\\n#[cfg(kani)]\\nextern crate alloc;\\n','',1);assert t==old[f]
f='programs/r1-cost-probe/src/r1_pool_adapter.rs';assert (s/f).read_text().removesuffix('\\n#[cfg(kani)]\\n#[path = "NCF_sdk.rs"]\\nmod NCF_sdk;\\n')==old[f]
patch='';snap={{}}
newnames=['crates/aspis-statement/src/NCF_policy.rs','crates/aspis-statement/src/pool_v1/NCF_slots.rs','programs/r1-cost-probe/src/NCF_sdk.rs']
for name in list(old)+newnames:
 text=(s/name).read_text();snap[name]=dict(sha256=sha(s/name),bytes=(s/name).stat().st_size,text=text)
 patch+=''.join(difflib.unified_diff(old.get(name,'').splitlines(True),text.splitlines(True),fromfile='a/'+name if name in old else '/dev/null',tofile='b/'+name))
changed=[];missing=[]
for name,want in blobs.items():
 p=s/name
 if not p.exists():missing.append(name);continue
 data=p.read_bytes();got=hashlib.sha1(b'blob '+str(len(data)).encode()+bytes([0])+data).hexdigest()
 if got!=want:changed.append(dict(path=name,sha256=hashlib.sha256(data).hexdigest()))
assert not missing,missing
assert set(x['path'] for x in changed)==set(old)|{{'crates/aspis-statement/src/pool_v1/pair_terminal.rs','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'}},changed
cache=pins['cache'];library=pins['library']
assert all(sha(Path(p))==v['sha256'] for p,v in cache.items())
assert all(sha(Path(p))==v['sha256'] for p,v in library.items())
c=Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028');final={{str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for p in c.rglob('*') if p.is_file()}}
# Only owned output directories are eligible for removal; never the retained cache.
cleanup=[]
for name in ['NCF_target','NCF_tmp']:
 p=b/name;assert p.parent==b and p.name.startswith('NCF_')
 size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file()) if p.exists() else 0
 if p.exists():shutil.rmtree(p)
 cleanup.append(dict(path=str(p),removed_bytes=size,exists_after=p.exists()))
result=dict(patch=patch,snapshots=snap,frozen_files=len(blobs),changed=changed,unchanged_frozen_files=len(blobs)-len(changed),imported_cache_unchanged=len(cache),Aeneas_unchanged=len(library),cache_end=final,cleanup=cleanup,non_cfg_body_changes=False,all70_terminal=True)
(b/"NCF_HOST_FINAL.json").write_text(json.dumps(result))
print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',m.H,'python3 -'],input=code,capture_output=True,text=True,timeout=90)
(E/'NCF_FINAL_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,transport='stdin; inline command previously300732 bytes reset repeatedly',prover_submission=False),indent=2))
assert r.returncode==0,r.stdout+r.stderr
x=json.loads(r.stdout);(E/'NCF_final_harness.patch').write_text(x.pop('patch'))
for name,v in x.pop('snapshots').items():
 p=E/'NCF_final_sources'/name;p=p.with_suffix(p.suffix+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v['text'])
(E/'NCF_HOST_FINAL.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:v for k,v in x.items() if k!='cache_end'}))
