"""Read-only pin verification, followed only by own rebuildable Rust cleanup."""
from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCM_host as h
r=h.remote_py(f'''from pathlib import Path
import json,hashlib,shutil
b=Path({h.B!r});cache=Path({h.CACHE!r})
# Every directly resolved input, including all resolved Aeneas objects, was
# recorded before its compile. Check their final content without rebuilding.
pins={{}}
for p in sorted(b.glob('NCM_L[0-9][0-9][0-9].json')):
 cfg=json.loads(p.read_text())
 for name,v in cfg.get('deps_fingerprint',{{}}).get('selected_objects',{{}}).items():
  if v['path'] in pins:assert pins[v['path']]==v['sha256'],('changed input object',v['path'])
  pins[v['path']]=v['sha256']
changes=[]
for p,sha in pins.items():
 actual=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 if sha!=actual:changes.append(dict(path=p,expected=sha,actual=actual))
assert not changes,changes
outputs={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in sorted(cache.glob('NCM_*.olean'))}}
# No key/account paths exist in this cleanup set: only Cargo/Kani artifacts.
removed=[]
for n in ['NCM_target','NCM_tmp']:
 p=b/n
 if p.exists():
  assert p.parent==b and p.name in ['NCM_target','NCM_tmp'] and not p.is_symlink()
  size=sum(f.stat().st_size for f in p.rglob('*') if f.is_file())
  shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
print(json.dumps(dict(verified_input_objects=len(pins),changes=changes,output_objects=outputs,removed_rebuildable_only=removed,retained_cache=str(cache),retained_source=str(b/'NCM_src'))))
''');assert r.returncode==0,r.stderr
(E/'NCM_FINAL_HOST_PINS.json').write_text(r.stdout)
out=json.loads(r.stdout);print({k:v for k,v in out.items() if k!='output_objects'})
