"""Read-only re-resolution/hashing of inherited and new selected objects."""
from pathlib import Path
import hashlib,json,lzma,subprocess
E=Path(__file__).resolve().parent
x=json.loads(lzma.decompress((E/'NIB_INHERITED_CLOSURE_INPUT.json.xz').read_bytes()))
config=json.loads((E/'NIB_L018.json').read_text())
code='''from pathlib import Path
import hashlib,json,lzma
B=Path('/home/dombarker/project-offloads/codex-cx-pool-settle-20261106')
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for buf in iter(lambda:f.read(1048576),b''):h.update(buf)
 return h.hexdigest()
roots=config['env']['LEAN_PATH'].split(':');out=[]
for r in baseline['selected_objects']:
 p=r['path'];old=next((z for z in sorted(baseline['LEAN_PATH'],key=len,reverse=True) if p.startswith(z+'/')),None)
 assert old,p
 rel=p[len(old)+1:];selected=next((Path(z)/rel for z in roots if (Path(z)/rel).is_file()),None)
 assert selected,rel
 sha=digest(selected);assert sha==r['sha256'],(str(selected),sha,r['sha256'])
 out.append(dict(path=str(selected),sha256=sha,bytes=selected.stat().st_size,baseline=p))
for folder in ['NIB_objects','NIB_native']:
 for p in (B/folder).glob('*'):
  if p.is_file():out.append(dict(path=str(p),sha256=digest(p),bytes=p.stat().st_size))
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 p=B/name
 if p.exists():out.append(dict(path=str(p),sha256=digest(p),bytes=p.stat().st_size))
result=dict(LEAN_PATH=roots,selected_objects=out,inherited_objects_verified=len(baseline['selected_objects']),inherited_hash_changes=0)
raw=json.dumps(result).encode();(B/'NIB_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NIB_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
print(json.dumps(dict(objects=len(out),inherited_verified=len(baseline['selected_objects']),hash_changes=0)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input='baseline='+repr(x)+'\nconfig='+repr(config)+'\n'+code,text=True,capture_output=True)
(E/'NIB_CLOSURE_TRANSPORT.log').write_text(r.stdout+r.stderr)
print(r.stdout,r.stderr);assert r.returncode==0
for name in ['NIB_CLOSURE_PINS.json.xz','NIB_CLOSURE_PINS.json.sha256']:
 r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-pool-settle-20261106/'+name],capture_output=True);assert r.returncode==0;(E/name).write_bytes(r.stdout)
