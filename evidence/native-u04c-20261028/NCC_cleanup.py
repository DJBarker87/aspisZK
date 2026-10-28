"""Verify retained objects and remove ONLY own disposable build output."""
from pathlib import Path
import json,hashlib,importlib.util,sys,zlib,base64,subprocess
E=Path(__file__).resolve().parent
initial=json.loads((E/'NCC_CACHE_IMPORTED.json').read_text());initial_digest=hashlib.sha256(json.dumps(initial,sort_keys=True,separators=(',',':')).encode()).hexdigest()
sys.argv=['ncc','none'];s=importlib.util.spec_from_file_location('ncc',E/'NCC_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
code='''from pathlib import Path
import json,hashlib,os,shutil,zlib,base64
b=Path(%r);cache=Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028')
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:args=(p/'cmdline').read_bytes().decode(errors='replace').split('\\0')
 except (OSError,ProcessLookupError):continue
 if len(args)<2:continue
 executable=Path(args[0]).name
 if executable in ['lean','kani-driver','cbmc','cargo','cargo-kani','rustc'] and any('NCC_' in a for a in args):active.append(dict(pid=int(p.name),args=args))
 if executable.startswith('python') and any(a.endswith(('NCC_gate.py','NCC_batch_host.py','S2W_run_host.py','S2W_lean_host.py')) for a in args[1:3]) and any('NCC_' in a for a in args[1:]):active.append(dict(pid=int(p.name),args=args))
assert not active,('own prover/controller remains',active)
pins={str(p.relative_to(cache)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}
imported={n:v for n,v in pins.items() if not n.startswith('NCC_')};digest=hashlib.sha256(json.dumps(imported,sort_keys=True,separators=(',',':')).encode()).hexdigest();assert digest==%r,'imported cache changed'
library=json.loads((b/'NCC_LIBRARY_PIN.json').read_text());assert all(hashlib.sha256(Path(n).read_bytes()).hexdigest()==v['sha256'] and Path(n).stat().st_size==v['bytes'] for n,v in library.items()),'resolved Aeneas library changed'
cache_report=dict(cache=str(cache),initial_files=len(imported),all_imported_unchanged=True,imported_canonical_sha256=digest,final_files=len(pins),new_files={n:v for n,v in pins.items() if n.startswith('NCC_')},cache_retained=True,library_objects=len(library),all_library_objects_unchanged=True,pins=pins)
removed=[]
for name in ['NCC_target','NCC_tmp']:
 p=b/name;assert p.parent==b and p.name.startswith('NCC_') and not p.is_symlink()
 size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file()) if p.exists() else 0
 if p.exists():shutil.rmtree(p)
 removed.append(dict(path=str(p),bytes=size,exists_after=p.exists()))
cleanup=dict(active_own_provers=active,removed=removed,cache_retained=True,receipts_and_sources_retained=True,wallet_or_key_operations=False)
(b/'NCC_CACHE_END.json').write_text(json.dumps(cache_report,indent=2));(b/'NCC_CLEANUP.json').write_text(json.dumps(cleanup,indent=2))
print(base64.b64encode(zlib.compress(json.dumps(dict(cache=cache_report,cleanup=cleanup)).encode(),9)).decode())
'''%(m.B,initial_digest)
r=m.py(code);assert r.returncode==0,r.stdout+r.stderr
x=json.loads(zlib.decompress(base64.b64decode(r.stdout)));(E/'NCC_CACHE_END.json').write_text(json.dumps(x['cache'],indent=2)+'\n');(E/'NCC_CLEANUP.json').write_text(json.dumps(x['cleanup'],indent=2)+'\n')
print(json.dumps({k:v for k,v in x['cache'].items() if k!='pins'}));print(json.dumps(x['cleanup']))
