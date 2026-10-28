from pathlib import Path
import sys,json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
h.admit('NBV_SETUP')
files=['crates/aspis-r1-cost-probe/src/'+n for n in ['lib.rs','candidate.rs','multiproof.rs']]
payload={f:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f],text=True) for f in files}
patch=R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch'
code=f'''from pathlib import Path
import shutil,json,hashlib,subprocess
b=Path({h.B!r});base=Path('/home/dombarker/project-offloads/codex-cx-native-tx1a-20261027/NBE_src');s=b/'NBV_src'
assert not s.exists()
for p in base.rglob('*'):
 rel=p.relative_to(base);q=s/rel
 if p.is_dir():q.mkdir(parents=True,exist_ok=True)
 elif p.name.startswith('NBE_'):continue
 else:q.symlink_to(p.resolve())
for name,text in {payload!r}.items():
 p=s/name;p.unlink();p.write_text(text)
p=s/'Cargo.lock';p.unlink();shutil.copyfile(base/'Cargo.lock',p)
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copyfile(Path('/home/dombarker/project-offloads/codex-cx-native-tx1c-20261027')/name,b/name)
(b/'NBV_sources').mkdir();(b/'NBV_tmp').mkdir()
cache=Path({h.CACHE!r});assert not cache.exists();shutil.copytree('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027',cache)
p=b/'NBV_KMX_copy_stubs.patch';p.write_text({patch.read_text()!r})
r=subprocess.run(['git','apply',str(p)],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stderr
# Apply patch verbatim at scratch root; Rust module path points there.
p=s/'crates/aspis-r1-cost-probe/src/lib.rs';p.write_text(p.read_text().replace('#![no_std]','#![no_std]\\n#![feature(allocator_api)]')+'\\n#[cfg(kani)]\\n#[path="../../../KMX_stubs.rs"]\\npub mod KMX_stubs;\\n')
out={{}}
for label,root in [('cache',str(cache)),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
out['copy_patch_sha256']=hashlib.sha256((b/'NBV_KMX_copy_stubs.patch').read_bytes()).hexdigest()
out['lock_sha256']=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest()
print(json.dumps(out))
'''
r=h.remote_py(code);assert r.returncode==0,r.stderr+r.stdout
(E/'NBV_INITIAL_HOST_PINS.json').write_text(r.stdout)
print('setup pinned',len(json.loads(r.stdout)['cache']))
