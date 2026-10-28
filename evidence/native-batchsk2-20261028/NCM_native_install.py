from pathlib import Path
import json,sys,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCM_host as h
h.admit('NCM_NATIVE_INSTALL')
patches={'NCM_native.patch':(E/'NCM_native.patch').read_text(),'NCM_KMX_copy_stubs.patch':(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text()}
assert hashlib.sha256(patches['NCM_KMX_copy_stubs.patch'].encode()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
r=h.remote_py(f'''from pathlib import Path
import subprocess,json,hashlib
b=Path({h.B!r});s=b/'NCM_src'
for n,text in {patches!r}.items():(b/n).write_text(text)
# These are inherited scratch-only KMX files, never release files.
for n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:
 p=s/n
 if p.exists():p.unlink()
for n in ['NCM_KMX_copy_stubs.patch','NCM_native.patch']:
 r=subprocess.run(['git','apply',str(b/n)],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stderr
print(json.dumps({{n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in {list(patches)!r}}}))
''');assert r.returncode==0,r.stderr
(E/'NCM_NATIVE_PATCH_PINS.json').write_text(r.stdout)
print(r.stdout)
