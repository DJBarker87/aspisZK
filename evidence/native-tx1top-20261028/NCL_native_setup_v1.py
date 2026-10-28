from pathlib import Path
import subprocess,json,hashlib,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCL_host as h
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
names=subprocess.check_output(['git','ls-tree','-r','--name-only',F],text=True).splitlines()
names=[n for n in names if n.startswith(('crates/','programs/')) or n in ['Cargo.lock','Cargo.toml']]
blobs={n:subprocess.check_output(['git','show',F+':'+n]) for n in names}
pins={n:hashlib.sha256(v).hexdigest() for n,v in blobs.items()}
(E/'NCL_FROZEN_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
h.admit('NCL_NATIVE_SETUP')
code=f'''from pathlib import Path
import json,hashlib
s=Path({(h.B+'/NCL_src')!r});old=Path('/home/dombarker/project-offloads/codex-cx-native-tx1f-20261028/NBY_src')
assert not s.exists();s.mkdir()
for p in old.rglob('*'):
 q=s/p.relative_to(old)
 if p.is_dir():q.mkdir(parents=True,exist_ok=True)
 else:q.symlink_to(p.resolve())
pins=json.loads({json.dumps(pins)!r});bad=[]
for n,expected in pins.items():
 p=s/n
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:bad.append(n)
print(json.dumps(bad))
'''
r=h.remote_py(code);(E/'NCL_NATIVE_SETUP-inventory.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
bad=json.loads(r.stdout);payload={n:blobs[n].decode() for n in bad}
patch=(Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch')).read_text()
assert hashlib.sha256(patch.encode()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
code=f'''from pathlib import Path
import json,subprocess,hashlib
b=Path({h.B!r});s=b/'NCL_src';files=json.loads({json.dumps(payload)!r});pins=json.loads({json.dumps(pins)!r})
for n,data in files.items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.is_symlink():p.unlink()
 p.write_text(data)
for n,want in pins.items():assert hashlib.sha256((s/n).read_bytes()).hexdigest()==want,n
# Freeze restoration succeeded before any Kani overlay.
for n in ['crates/aspis-core/src/lib.rs','crates/aspis-core/src/r0/heap.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/verifier.rs','programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/pool_route.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs']:
 p=s/n;data=p.read_bytes()
 if p.is_symlink():p.unlink();p.write_bytes(data)

for name in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:
 p=s/name
 if p.exists() or p.is_symlink():p.unlink()
patch={patch!r};(b/'NCL_KMX_copy_stubs.patch').write_text(patch)
r=subprocess.run(['git','apply','--unsafe-paths','-'],cwd=s,input=patch,text=True,capture_output=True);assert r.returncode==0,r.stderr
(b/'NCL_tmp').mkdir(exist_ok=True)
print(json.dumps(dict(restored=len(files),frozen_files=len(pins),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),copy_patch_sha256=hashlib.sha256(patch.encode()).hexdigest())))
'''
r=h.remote_py(code);(E/'NCL_NATIVE_SETUP-overlay.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
print(r.stdout)
