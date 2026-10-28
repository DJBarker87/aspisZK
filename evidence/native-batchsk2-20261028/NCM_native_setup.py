from pathlib import Path
import subprocess,hashlib,json,sys,tempfile,time,gzip,shlex
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCM_host as h
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
h.admit('NCM_NATIVE_SETUP')
r=h.remote_py(f'''from pathlib import Path
import shutil,json,hashlib
b=Path({h.B!r});s=b/'NCM_src';assert not s.exists(),'own source already exists; reuse rather than clone'
seed=Path('/home/dombarker/project-offloads/codex-cx-native-tx1e-20261028/NBV_src')
print(json.dumps({{str(p.relative_to(seed)):hashlib.sha256(p.read_bytes()).hexdigest() for p in seed.rglob('Cargo.toml')}}))
shutil.copytree(seed,s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
(b/'NCM_tmp').mkdir(exist_ok=True)
''');assert r.returncode==0,r.stderr
(E/'NCM_NATIVE_SEED_PINS.json').write_text(r.stdout)
raw=subprocess.check_output(['git','archive',rev,'Cargo.toml','Cargo.lock','crates','programs'])
p=Path(tempfile.gettempdir())/'NCM-native-source.tar.gz';p.write_bytes(gzip.compress(raw))
try:
 for trial in range(10):
  r=subprocess.run(['scp','-o','ConnectTimeout=15',str(p),h.H+':'+h.B+'/NCM-native-source.tar.gz'],capture_output=True,text=True)
  with (E/'NCM_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(step='native upload',trial=trial,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode==0:break
  if r.returncode!=255 or trial==9:raise SystemExit('STOP upload failed')
  time.sleep(60)
finally:p.unlink()
r=h.remote_py(f'''from pathlib import Path
import tarfile,hashlib,json
b=Path({h.B!r});s=b/'NCM_src'
with tarfile.open(b/'NCM-native-source.tar.gz') as f:f.extractall(s,filter='data')
(b/'NCM-native-source.tar.gz').unlink()
print(json.dumps({{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for d in ['crates','programs'] for p in (s/d).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']}}))
''');assert r.returncode==0,r.stderr
(E/'NCM_NATIVE_RESTORED_PINS.json').write_text(r.stdout)
print('one private scratch seeded; frozen tracked Rust restored; seed manifests pinned')
