from pathlib import Path
import subprocess,json,hashlib,lzma
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-pool-b3-20261106';C='/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';H='dombarker@100.108.41.90'
modules=[json.loads(l)['module'] for l in(E/'NHP_LOADED_scan.jsonl').read_text().splitlines()]
code='''from pathlib import Path
import hashlib,json,subprocess,sys,shutil,lzma
b=Path(B);c=Path(C);q=b/'NHP_EXPORT-admission.json'
with(b/'NHP_EXPORT-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(q.read_text())
if r.returncode or a.get('allowed') is not True:print(json.dumps(dict(admission=a,exit=r.returncode)));sys.exit(78)
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
roots=json.loads((b/'NHP_L023.json').read_text())['env']['LEAN_PATH'].split(':');selected=[]
for module in modules:
 rel=module.replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if(Path(root)/rel).is_file()),None);assert p,module
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():selected.append(dict(module=module,path=str(z),sha256=digest(z),bytes=z.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=selected)).encode();(b/'NHP_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(b/'NHP_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
dest=c/'NHP_exports_20261106';dest.mkdir(exist_ok=True);exports=[]
for p in (b/'NHP_objects').rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(b/'NHP_objects');z=dest/rel;z.parent.mkdir(parents=True,exist_ok=True)
 if not z.exists():shutil.copy2(p,z)
 assert digest(z)==digest(p),str(z)
 exports.append(dict(path=str(z),source=str(p),sha256=digest(z),bytes=z.stat().st_size))
native=c/'NHP_native_exports_20261106';native.mkdir(exist_ok=True)
for p in (b/'NHP_native').iterdir():
 if not p.is_file():continue
 z=native/p.name
 if not z.exists():shutil.copy2(p,z)
 assert digest(z)==digest(p)
 exports.append(dict(path=str(z),source=str(p),sha256=digest(z),bytes=z.stat().st_size))
(b/'NHP_EXPORT.json').write_text(json.dumps(dict(cache_retained=C,admission=a,exit=r.returncode,exports=exports,selected_objects=len(selected),selected_bytes=sum(z['bytes'] for z in selected)),indent=1)+'\\n')
print(json.dumps(dict(exports=len(exports),objects=len(selected),bytes=sum(z['bytes'] for z in selected))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nW='+repr(W)+'\nT='+repr(T)+'\nmodules='+repr(modules)+'\n'+code,text=True,capture_output=True);(E/'NHP_EXPORT.log').write_text(r.stdout+r.stderr);print(r.stdout[-1200:],r.stderr[-700:]);assert r.returncode==0,r.returncode
for n in ['NHP_EXPORT.json','NHP_CLOSURE_PINS.json.xz','NHP_CLOSURE_PINS.json.sha256','NHP_EXPORT-admission.json','NHP_EXPORT-barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
