"""Hash-checked read-only seed; hardlinks only within our retained ledger8 cache."""
from pathlib import Path
import json,subprocess,time,re
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger11-20261107';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NII_flat'
files=[];provenance=[]
for a in ['NHK','NHN','NHG','NHS','NHM','NHJ','NHX','NHU','NHP','NHZ','NIB','NHW','NIF']:
 d=next(E.parent.glob('*/'+a+'_HANDOFF.md')).parent
 ps=list(d.glob(a+'*EXPORT.json'))+list(d.glob(a+'_FINAL_HOST.json'))+list(d.glob(a+'_HOST_END.json'))
 for p in ps:
  x=json.loads(p.read_text());root=x.get('export',x.get('export_path',x.get('destination','')))
  rows=x.get('files',x.get('exports',x.get('objects',x.get('exported_files',[]))))
  rows=list(rows.values())if isinstance(rows,dict)else rows
  for f in rows:
   path=f.get('retained',f.get('destination',f.get('path','')))
   if not path.startswith('/') and root:path=root+'/'+path
   if not path.endswith('.olean'):continue
   tail=re.split(r'/[^/]*exports[^/]*/',path)[-1];rel=f.get('relative_path',tail.removeprefix('objects/') if tail!=path else Path(path).name)
   files.append(dict(source=path,relative=rel,sha256=f['sha256']))
  provenance.append(str(p))
(E/'NII_SEED_INPUTS.json').write_text(json.dumps(dict(files=files,provenance=provenance),indent=1)+'\n')
code='''from pathlib import Path
import json,hashlib,lzma,shutil,subprocess,sys,os
b=Path(B);c=Path(C);b.mkdir(exist_ok=True);c.mkdir(exist_ok=True)
with (b/'NII_SEED_RESERVATION.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NII_SEED_RESERVATION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NII_SEED_RESERVATION.json').read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode!=0 or a.get('allowed')is not True:sys.exit(78)
base=c.parent/'NHO_flat';rows=[]
# Remove only the erroneous own flat Types copy from seed v1 (namespace repair).
for name in ['Types.olean','Types.olean.private','Types.olean.server','Types.ir']:
 p=c/name
 if p.exists():p.unlink()
for p in base.rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(base)
 if rel.parts[0].startswith('NHO_'):continue
 q=c/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():os.link(p,q)
 assert p.stat().st_size==q.stat().st_size
 rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size,method='owned-cache hardlink'))
for f in files:
 p=Path(f['source']);assert p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'],str(p)
 rel=Path(f['relative'])
 for source in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not source.is_file():continue
  q=c/rel.parent/source.name;q.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(source.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,('seed conflict',str(q))
  else:shutil.copy2(source,q)
  rows.append(dict(source=str(source),destination=str(q),sha256=h,bytes=source.stat().st_size,method='copy read-only export'))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
raw=json.dumps(dict(selected=rows,paths=len(rows),logical_bytes=sum(r['bytes']for r in rows),external_copy_bytes=sum(r['bytes']for r in rows if r['method'].startswith('copy')),admission=a,exit=r.returncode)).encode()
(b/'NII_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NII_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n');print(json.dumps(dict(paths=len(rows),bytes=sum(r['bytes']for r in rows),disk_free=shutil.disk_usage(b).free)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nfiles='+repr(files)+'\n'+code,capture_output=True,text=True)
 (E/f'NII_SEED_TRANSPORT_{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-1200:],r.stderr[-1200:],flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,255]or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for name in ['NII_CACHE_IMPORTS.json.xz','NII_CACHE_IMPORTS.json.sha256','NII_SEED_RESERVATION.json','NII_SEED_RESERVATION.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+name],capture_output=True);assert r.returncode==0;(E/name).write_bytes(r.stdout)
