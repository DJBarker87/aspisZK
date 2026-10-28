from pathlib import Path
import sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCM_host as h
h.admit('NCM_SETUP')
r=h.remote_py(f'''from pathlib import Path
import shutil,json,hashlib
b=Path({h.B!r});old=Path('/home/dombarker/project-offloads/codex-cx-native-batchsk-20261028')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copyfile(old/n,b/n)
(b/'NCM_sources').mkdir(exist_ok=True)
out={{}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
print(json.dumps(out))''')
assert r.returncode==0,r.stderr
(E/'NCM_INITIAL_HOST_PINS.json').write_text(r.stdout)
print('Pinned existing batch cache and coherent/Aeneas objects; launchers copied unchanged')
