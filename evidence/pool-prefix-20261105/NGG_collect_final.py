from pathlib import Path
import subprocess,json,time,lzma,hashlib
E=Path(__file__).resolve().parent
code=r'''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-pool-prefix-20261104');cache=b.parent/'codex-cx-pool-prefix-cache-20261104';out={}
assert (b/'NGG_B060/receipt.json').exists()
for p in [b/'NGG_LOADED.jsonl',*b.glob('NEP_final_*_REACHABLE.txt'),*b.glob('NEP_fixtures_*_REACHABLE.txt')]:
 out[p.name]=p.read_text()
paths=[json.loads(l) for l in (b/'NGG_LOADED.jsonl').read_text().splitlines()]
objects={}
for row in paths:
 p=Path(row['path']);assert p.exists(),p
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.exists() and str(q) not in objects:objects[str(q)]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
out['NGG_RESOLVED_OBJECTS.json']=json.dumps(dict(modules=len(paths),objects=objects),indent=1)+'\n'
dest=cache/'NGG_final_objects_20261105';dest.mkdir(exist_ok=True);export=[]
for root in ['NGG_B_objects','NGG_C_objects','NGG_B_generated','NGG_C_generated']:
 if not (b/root).exists():continue
 for p in (b/root).rglob('*'):
  if not p.is_file():continue
  rel=p.relative_to(b/root);q=dest/rel
  if q.exists():assert q.read_bytes()==p.read_bytes(),('different own export',str(q));continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);export.append(dict(path=str(q),source=str(p),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
# Retain exact native audit build inputs, never executable files in Git.
for p in (b/'NFO_native').glob('NGG_*'):
 if not p.is_file():continue
 q=cache/'NGG_audit_native_20261105'/p.name;q.parent.mkdir(exist_ok=True);shutil.copy2(p,q);export.append(dict(path=str(q),source=str(p),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
out['NGG_EXPORTS.json']=json.dumps(dict(exports=export,bytes=sum(x['bytes'] for x in export),cache=str(cache),cache_bytes=sum(p.stat().st_size for p in cache.rglob('*') if p.is_file()),cache_retained=True),indent=1)+'\n'
print(json.dumps(out))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():
 data=s.encode()
 if n=='NGG_RESOLVED_OBJECTS.json' or len(data)>19_000_000:
  p=E/(n+'.xz');p.write_bytes(lzma.compress(data));(E/(n+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'  '+n+'\n');(E/(n+'.xz.sha256')).write_text(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n')
 else:(E/n).write_text(s)
print(json.dumps(dict(files=len(out),modules=len(out['NGG_LOADED.jsonl'].splitlines()),export_bytes=json.loads(out['NGG_EXPORTS.json'])['bytes'])))
