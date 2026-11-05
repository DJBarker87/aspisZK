from pathlib import Path
import json,subprocess,time,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-d-parser3-20261105'
modules=[p.stem for p in E.glob('NGV_*.lean') if p.stem!='NGV_COMBINED_IMPORT' and '#print axioms ' in p.read_text() and 'namespace NGV_' in p.read_text()]+['NGV_COMBINED_IMPORT']
code=f'''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path({B!r});ad=b/'NGV_export-admission.json'
with (b/'NGV_export-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(ad)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(ad.read_text());assert r.returncode==0 and a.get('allowed') is True,(r.returncode,a)
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-parser2-cache-20261104/NGV_exports_20261105');cache.mkdir(exist_ok=True)
files=[]
for name in {modules!r}:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=b/'NGV_objects'/(name+suffix)
  if p.is_file():
   q=cache/p.name;assert not q.exists();shutil.copy2(p,q)
   files.append(dict(path=str(q),source=str(p),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
x=dict(admission=a,exit=r.returncode,files=files,bytes=sum(p['bytes'] for p in files),source_revision={subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()!r},source_tree_dirty=True)
(b/'NGV_CACHE_EXPORTS.json').write_text(json.dumps(x,indent=2));print(json.dumps(x))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 (E/f'NGV_EXPORT-transport-{retry}.log').write_text(r.stderr)
 if r.returncode==0:
  (E/'NGV_CACHE_EXPORTS.json').write_text(r.stdout);x=json.loads(r.stdout);print('Retained',len(x['files']),'files /',x['bytes'],'bytes');break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 raise RuntimeError('Export preparation failed: '+r.stderr)
