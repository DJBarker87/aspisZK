from pathlib import Path
import json,subprocess,lzma,time,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger10-20261106';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NHO_flat'
exports=[]
for a in ['NGW','NGY','NGX','NHE','NHF','NHI','NHH','NHC']:
 d=next(E.parent.glob('*/'+a+'_HANDOFF.md')).parent;p=d/(a+'_EXPORT.json')
 if p.exists():
  x=json.loads(p.read_text());root=x.get('export',x.get('exports',''))
  for f in x.get('files',x.get('copied',x.get('exports',[]))):
   if not isinstance(f,dict):continue
   path=f.get('destination',f.get('path',''))
   if not path.startswith('/') and isinstance(root,str):path=root+'/'+path
   if any(path.endswith(s)for s in ['.olean','.olean.private','.olean.server','.ir']):
    rel=path.split('/'+a+'_exports',1)[1].split('/',1)[1] if '/'+a+'_exports'in path else Path(path).name
    if rel.startswith('objects/'):rel=rel[len('objects/'):]
    exports.append(dict(source=path,relative=rel,sha256=f['sha256'],bytes=f['bytes']))
x=json.loads((E.parent/'slice-d-finish2-20261105/NGW_EXPORT_MANIFEST.json').read_text())
for f in x['files_manifest']:
 if any(f['path'].endswith(t) for t in ['.olean','.olean.private','.olean.server','.ir']):
  rel=f['path'].removeprefix('objects/');exports.append(dict(source=x['path']+'/'+f['path'],relative=rel,sha256=f['sha256'],bytes=f['bytes']))
code='''from pathlib import Path
import json,hashlib,lzma,shutil,subprocess,sys,os
b=Path(B);c=Path(C);b.mkdir(exist_ok=True);c.mkdir(exist_ok=True)
with (b/'NHO_SEED_RESERVATION.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHO_SEED_RESERVATION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NHO_SEED_RESERVATION.json').read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode!=0 or a.get('allowed')is not True:sys.exit(78)
base=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGZ_flat');rows=[]
# Predecessor and current job share OWN retained cache. Hardlinks only there,
# never mutate linked files; read-only external exports are copied separately.
for p in base.rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(base)
 if rel.parts[0].startswith('NGZ_'):continue
 q=c/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():os.link(p,q)
 h=hashlib.sha256(q.read_bytes()).hexdigest();rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size,method='identical owned-cache hardlink'))
# NGZ retained exports are nested; include selected modules, never drivers.
for p in (base/'NGZ_exports_20261105').glob('*'):
 if p.is_file() and not p.name.startswith('NGZ_'):
  q=c/p.name
  if not q.exists():os.link(p,q)
# Explicit export paths retain namespace directories, including extracted Types.
seen={}
for f in exports:
 p=Path(f['source']);assert p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'],('export hash',str(p))
 for source,rel in [(p,f['relative'])]+[(Path(str(p)+suffix),f['relative']+suffix)for suffix in ['.private','.server'] if p.name.endswith('.olean')]+[(p.with_suffix('.ir'),str(Path(f['relative']).with_suffix('.ir')))for _ in [0]if p.name.endswith('.olean')]:
  if not source.is_file():continue
  q=c/rel;q.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(source.read_bytes()).hexdigest()
  if rel in seen:assert seen[rel]==h,('conflicting export',rel)
  seen[rel]=h
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,('conflicting seed',str(q))
  else:shutil.copy2(source,q)
  rows.append(dict(source=str(source),destination=str(q),sha256=h,bytes=source.stat().st_size,method='copy external read-only export'))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
raw=json.dumps(dict(selected=rows,paths=len(rows),logical_bytes=sum(r['bytes']for r in rows),external_copy_bytes=sum(r['bytes']for r in rows if r['method'].startswith('copy')),admission=a,exit=r.returncode)).encode()
(b/'NHO_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NHO_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n');print(json.dumps(dict(paths=len(rows),bytes=sum(r['bytes']for r in rows))))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nexports='+repr(exports)+'\n'+code,capture_output=True,text=True)
 (E/f'NHO_SEED4_TRANSPORT_{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-1200:],r.stderr[-1200:],flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,255]or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for name in ['NHO_CACHE_IMPORTS.json.xz','NHO_CACHE_IMPORTS.json.sha256','NHO_SEED_RESERVATION.json','NHO_SEED_RESERVATION.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+name],capture_output=True);assert r.returncode==0;(E/name).write_bytes(r.stdout)
