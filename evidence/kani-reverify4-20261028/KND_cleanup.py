"""Final own-artifact cleanup and read-only pin audit; no build or cache removal."""
from KND_driver import *
baseline=json.loads((E.parent/'kani-reverify2-20261028/KMZ_CLEANUP.json').read_text())['baseline_pins_unchanged']
code='''from pathlib import Path
import hashlib,json,subprocess,shutil,datetime
b=Path('''+repr(t.B)+''');cache=Path('''+repr(t.CACHE)+''');baseline='''+repr(baseline)+'''
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
rows=subprocess.check_output(['ps','-eo','pid=,args='],text=True).splitlines()
live=[x for x in rows if x.split(None,1)[1].startswith('python3 S2W_run_host.py KND_') or (x.split(None,1)[1].split()[0].endswith('/kani-driver') and 'KND_windows' in x)]
assert not live,live
pins={}
for name,pin in baseline.items():
 p=Path(pin['path']);sha=digest(p);assert sha==pin['sha256'],name
 pins[name]=dict(path=str(p),sha256=sha,bytes=p.stat().st_size)
sourcepins={str(p.relative_to(b)):digest(p) for p in [b/'KMX_stubs.rs',b/'KMY_src/Cargo.lock']}
assert sourcepins['KMX_stubs.rs']==''' + repr(STUB)+'''
assert sourcepins['KMY_src/Cargo.lock']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
removed=[]
p=b/'KND_native_bin'
if p.exists():
 with p.open('rb') as f:assert f.read(4)==b'\\x7fELF'
 removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=digest(p)));p.unlink()
temps=[]
for p in b.glob('KND_KND_K*_tmp_*'):
 assert p.is_dir() and not p.is_symlink()
 temps.append(dict(path=str(p),bytes=sum(x.stat().st_size for x in p.rglob('*') if x.is_file())));shutil.rmtree(p)
objects={p.name:dict(sha256=digest(p),bytes=p.stat().st_size) for p in cache.glob('KND_*.olean')}
candidates=[dict(path=str(p),bytes=p.stat().st_size) for p in b.glob('KND_windows*') if p.is_file() and p.suffix!='.rs']
print(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),live_own_processes=live,retained_cache=str(cache),persistent_cache_deleted=False,baseline_pins_unchanged=pins,retained_new_objects=objects,source_pins=sourcepins,removed_compiler_scratch=removed,removed_owned_temp_directories=temps,remaining_compiler_candidates=candidates,shared_unattributed_temporaries='retained; never deleted'),indent=2))
'''
r=t.remote_py(code);assert r.returncode==0,r.stderr
(E/'KND_CLEANUP.json').write_text(r.stdout);print(r.stdout)
