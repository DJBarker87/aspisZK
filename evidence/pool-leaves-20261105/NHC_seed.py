from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;P=E.parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-pool-leaves-20261105';C='/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104'
x=json.loads(lzma.decompress((P/'pool-retarget-20261105/NGK_CLOSURE_PINS.json.xz').read_bytes()));selected={}
for r in x['selected_objects']:
 p=r['path'];root=next(z for z in x['LEAN_PATH'] if p.startswith(z+'/'))
 if '/.elan/' in p:continue
 rel=p[len(root)+1:]
 if '/NGK_objects/' in p:p=p.replace('/codex-cx-pool-retarget-20261105/NGK_objects/','/codex-cx-pool-retarget-cache-20261104/NGK_exports_20261105/')
 selected.setdefault(rel,dict(source=p,relative=rel,sha256=r['sha256'],bytes=r['bytes']))
for r in json.loads((P/'pool-retarget-20261105/NGK_EXPORT.json').read_text())['exports']:
 if '/NGK_exports_20261105/' in r['path']:
  rel=r['path'].split('/NGK_exports_20261105/')[1];selected.setdefault(rel,dict(source=r['path'],relative=rel,sha256=r['sha256'],bytes=r['bytes']))
files=list(selected.values());raw=json.dumps(files).encode();(E/'NHC_SEED_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'NHC_SEED_INPUTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
remote='''from pathlib import Path
import hashlib,json,subprocess,sys,shutil,lzma
b=Path(B);b.mkdir(exist_ok=True);c=Path(C);dest=c/'NHC_seed';dest.mkdir(exist_ok=True)
with (b/'NHC_SEED_RESERVATION.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHC_SEED_RESERVATION.json')],stdout=f,stderr=subprocess.STDOUT)
x=json.loads((b/'NHC_SEED_RESERVATION.json').read_text());print(json.dumps(x),flush=True)
if r.returncode!=0 or x.get('allowed') is not True:sys.exit(78)
rows=[]
for row in files:
 rel=row['relative'];p=Path(row['source']);z=c/rel;q=dest/rel
 # Existing job cache objects can be reused only at the pinned exact hash.
 if z.is_file() and hashlib.sha256(z.read_bytes()).hexdigest()==row['sha256']:
  rows.append(dict(row,destination=str(z),copied=False));continue
 assert p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256'],str(q)
 rows.append(dict(row,destination=str(q),copied=True))
raw=json.dumps(dict(imports=rows,seed_bytes=sum(r['bytes'] for r in rows if r['copied']),reused_bytes=sum(r['bytes'] for r in rows if not r['copied']))).encode()
(b/'NHC_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NHC_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
for n in ['S2W_run_host.py','S2W_lean_host.py']:
 p=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')/n;q=b/n
 if not q.exists():shutil.copy2(p,q)
 assert p.read_bytes()==q.read_bytes()
print(json.dumps(dict(files=len(rows),copied_bytes=sum(r['bytes'] for r in rows if r['copied']))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nfiles='+repr(files)+'\n'+remote,text=True,capture_output=True);(E/'NHC_SEED_TRANSPORT.log').write_text(r.stdout+r.stderr);print(r.stdout[-1500:],r.stderr[-1500:]);assert r.returncode==0,r.returncode
for n in ['NHC_CACHE_IMPORTS.json.xz','NHC_CACHE_IMPORTS.json.sha256','NHC_SEED_RESERVATION.json','NHC_SEED_RESERVATION.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
