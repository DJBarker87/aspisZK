from pathlib import Path
import hashlib,json,subprocess,sys
B=Path(__file__).resolve().parent;c=B/sys.argv[1];x=json.loads(c.read_text());paths=x['env']['LEAN_PATH'].split(':');seen={}
def visit(module):
 key=module.replace('.','/')+'.olean'
 if key in seen:return
 p=next((Path(root)/key for root in paths if (Path(root)/key).is_file()),None)
 if p is None:raise FileNotFoundError(module)
 seen[key]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
 # All imported module dependencies are already inventoried in the inherited S2I
 # cache packet; the direct import and its split companions are re-pinned here.
 for suffix in ['.server','.private','.ir']:
  q=p.with_suffix('.ir') if suffix=='.ir' else Path(str(p)+suffix)
  if q.exists():seen[str(q)]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
for src in x['sources']:
 for line in (B/src).read_text().splitlines():
  if line.startswith('import '):
   for module in line[7:].split():visit(module)
(B/'lakefile.toml').write_text('name = "s2z"\nversion = "0.1.0"\n');(B/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
x['deps_fingerprint']['selected_objects']=seen
x['deps_fingerprint']['lean_binary_sha256']=hashlib.sha256(Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean').read_bytes()).hexdigest()
current_sources={src:hashlib.sha256((B/src).read_bytes()).hexdigest() for src in x['sources']}
for previous in B.glob('lean-*/receipt.json'):
 old=json.loads(previous.read_text())
 if old.get('source_hashes')==current_sources and old.get('deps_fingerprint',{}).get('selected_objects')==seen:
  raise RuntimeError('Refusing unchanged source+dependencies: '+str(previous))
c.write_text(json.dumps(x,indent=2)+'\n')
r=subprocess.run([sys.executable,str(B/'S2Z_run_host.py'),sys.argv[1]]);sys.exit(r.returncode)
