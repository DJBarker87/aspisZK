from pathlib import Path
import sys,json,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCL_host as h
pins=json.loads((E/'NCL_FROZEN_PINS.json').read_text());lib=json.loads((E/'NCL_LIBRARY_RESOLVED.json').read_text())
code=f'''from pathlib import Path
import json,hashlib,subprocess,re
b=Path({h.B!r});s=b/'NCL_src';c=Path('/home/dombarker/project-offloads/codex-cx-tx1top-cache-20261028')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
lock=s/'Cargo.lock'
lock_info=dict(path=str(lock),is_symlink=lock.is_symlink(),resolved=str(lock.resolve()),sha256=sha(lock))
pins=json.loads({json.dumps(pins)!r});changed=[n for n,h in pins.items() if sha(s/n)!=h]
assert sorted(changed)==sorted(['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs']),changed
library=json.loads({json.dumps(lib)!r});assert all(sha(Path(p))==v['sha256'] for p,v in library.items()),'Aeneas library mutation'
rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
live=[x for x in rows if re.match(r'^(?:/usr/bin/)?python3 S2W_(?:run|lean)_host[.]py NCL_',x.strip())]
assert not live,live
cache={{str(p.relative_to(c)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in c.rglob('*') if p.is_file()}}
print(json.dumps(dict(lock=lock_info,changed_frozen_paths=changed,Aeneas_objects_and_sidecars_unchanged=len(library),own_cache=str(c),cache=cache,observed_live_own_launchers=live,launchers={{n:sha(b/n) for n in ['S2W_lean_host.py','S2W_run_host.py']}})))
'''
r=h.remote_py(code);(E/'NCL_POSTFLIGHT.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NCL_POSTFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='cache'}))
