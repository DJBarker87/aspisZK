from pathlib import Path
import json,hashlib,shutil,os
B=Path.cwd();D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJX_20261108');D.mkdir(exist_ok=True)
files=[]
for name in ['NJX_objects','NJX_priority','NJX_seed','NJX_NJO_seed']:
 src=B/name;dst=D/name
 assert not dst.exists(),'Never overwrite retained export'
 shutil.copytree(src,dst)
 for p in sorted(dst.rglob('*')):
  if p.is_file():files.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
S=D/'NJX_sources';S.mkdir(exist_ok=True)
for p in B.glob('NJX_*.lean'):
 shutil.copy2(p,S/p.name)
 q=S/p.name;files.append(dict(path=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
c=json.loads((B/'NJX_L149.json').read_text());paths=c['env']['LEAN_PATH'].split(':');paths=[str(D/Path(p).name) if Path(p).parent==B else p for p in paths]
pins=[]
for name in ['Aeneas','AeneasMeta']:
 for p in paths:
  f=Path(p)/(name+'.olean')
  if f.exists():pins.append(dict(module=name,path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size));break
 assert pins[-1]['module']==name
x=dict(status='RETAINED',source_revision=c['source_revision'],export_dir=str(D),LEAN_PATH=':'.join(paths),files=files,bytes=sum(p['bytes']for p in files),library_pins=pins,seed_order=['NJL','NJO'],cache_retained=True,CARGO_TARGET_DIR=str(B/'NJX_target'),no_target_deletion=True,disk_free=shutil.disk_usage(B).free)
(B/'NJX_EXPORT.json').write_text(json.dumps(x,indent=1));(D/'NJX_EXPORT.json').write_text(json.dumps(x,indent=1));print(json.dumps({k:x[k]for k in ['status','bytes','disk_free']}))
