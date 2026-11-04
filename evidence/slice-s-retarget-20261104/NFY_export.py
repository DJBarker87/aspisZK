"""Pin the actually resolved closure and retain owned exports without deleting cache."""
from pathlib import Path
import json,hashlib,lzma,os,subprocess
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-s-retarget-20261104';C=P/'codex-cx-slice-s-retarget-cache-20261104'
x=json.loads((B/'NFY_L110.json').read_text());roots=[Path(p) for p in x['env']['LEAN_PATH'].split(':')];scan=[json.loads(l) for l in (B/'NFY_LOADED_scan.jsonl').read_text().splitlines()];pins=[]
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for row in scan:
 module=row['module'];rel=module.replace('.','/')+'.olean';p=next((r/rel for r in roots if (r/rel).is_file()),None);assert p is not None,module
 fs={str(q):H(q) for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')] if q.is_file()}
 pins.append(dict(module=module,path=str(p),files=fs))
raw=json.dumps(dict(lean_path=[str(p) for p in roots],module_count=len(pins),selected=pins),sort_keys=True).encode();(B/'NFY_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NFY_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
D=C/'NFY_exports_20261104';D.mkdir(exist_ok=True);exports=[]
for p in sorted((B/'NFY_objects').iterdir()):
 if not p.is_file() or not any(p.name.endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
 q=D/p.name
 if not q.exists():os.link(p,q)
 assert H(q)==H(p);exports.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size))
for p in sorted((B/'NFY_generated').glob('NFY_*.lean')):
 q=D/p.name
 if not q.exists():os.link(p,q)
 assert H(q)==H(p);exports.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size))
N=C/'NFY_native_20261104';N.mkdir(exist_ok=True)
for p in sorted((B/'NFY_native').iterdir()):
 if not p.is_file():continue
 q=N/p.name
 if not q.exists():os.link(p,q)
 assert H(q)==H(p);exports.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size))
manifest=dict(cache_retained=str(C),workspace_retained=str(B),exports=exports,closure_manifest_sha256=H(B/'NFY_CLOSURE_PINS.json.xz'),disk=subprocess.check_output(['df','-h',str(B)],text=True),note='Owned exports hardlink owned output bytes; no predecessor cache, key, source or object was deleted or modified.')
(B/'NFY_EXPORT.json').write_text(json.dumps(manifest,indent=1)+'\n');print(json.dumps(dict(closure_modules=len(pins),exports=len(exports),closure_raw_sha256=hashlib.sha256(raw).hexdigest(),disk=manifest['disk'])))
