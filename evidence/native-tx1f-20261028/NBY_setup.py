from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBY_host as h
h.admit('NBY_SETUP')
r=h.remote_py(f'''from pathlib import Path
import shutil,json,hashlib
b=Path({h.B!r});old=Path('/home/dombarker/project-offloads/codex-cx-native-tx1e-20261028');s=b/'NBY_src';assert not s.exists();s.mkdir()
for p in (old/'NBV_src').rglob('*'):
 rel=p.relative_to(old/'NBV_src');q=s/rel
 if p.is_dir():q.mkdir(parents=True,exist_ok=True)
 else:q.symlink_to(p.resolve())
for name in ['Cargo.lock','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/multiproof.rs']:
 p=s/name;data=p.read_bytes();p.unlink();p.write_bytes(data)
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copyfile(old/name,b/name)
(b/'NBY_sources').mkdir();(b/'NBY_tmp').mkdir()
shutil.copyfile(old/'NBV_KMX_copy_stubs.patch',b/'NBY_KMX_copy_stubs.patch')
out={{}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
out['copy_patch_sha256']=hashlib.sha256((b/'NBY_KMX_copy_stubs.patch').read_bytes()).hexdigest();assert out['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
out['lock_sha256']=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest()
print(json.dumps(out))
''')
assert r.returncode==0,r.stdout+r.stderr
(E/'NBY_INITIAL_HOST_PINS.json').write_text(r.stdout)
r=h.remote_py(f'from pathlib import Path\nPath({(h.B+"/NBY_gate.py")!r}).write_text({(E/"NBY_gate.py").read_text()!r})');assert r.returncode==0,r.stderr
print('pinned cache and Aeneas; existing batch cache retained')
