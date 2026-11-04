"""Own cache seed, verified exports first; no shared infrastructure writes."""
from pathlib import Path
import subprocess,json,lzma,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-q-accum-20261104'
C='/home/dombarker/project-offloads/codex-cx-slice-q-accum-cache-20261104'
H='dombarker@100.108.41.90'
pins=json.loads((E.parent/'slice-q-values-20261104/NFP_EXPORT.json').read_text())['files']
n=json.loads((E.parent/'slice-q-phase-20261104/NFN_OBJECT_EXPORTS.json').read_text())
for row in n['objects']:
 pins += row['files']
code=f'''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path({B!r});b.mkdir(exist_ok=True)
with (b/'NFS_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NFS_SETUP-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NFS_SETUP-admission.json';print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
a=json.loads(p.read_text())
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(78)
for x in json.loads({json.dumps(pins)!r}):
 p=Path(x.get('destination',x.get('path')));assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'],str(p)
c=Path({C!r});c.mkdir(exist_ok=True);records=[]
seeds=['codex-cx-slice-q-values-cache-20261104','codex-cx-slice-q-phase-cache-20261104','codex-cx-slice-q-mul9-cache-20261104','codex-cx-slice-q-compose6-cache-20261104','codex-cx-leaf-cache-20261027','codex-cx-cpilot-cache-20261028']
for seed in seeds:
 root=b.parent/seed
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  if not any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir','.lean']):continue
  rel=p.relative_to(root);q=c/rel
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
  h=hashlib.sha256(q.read_bytes()).hexdigest();assert h==hashlib.sha256(p.read_bytes()).hexdigest()
  records.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
w=b.parent/'codex-cx-sound-int2-20261025'
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:(b/name).write_bytes((w/name).read_bytes())
for name in ['NFS_objects','NFS_tmp','NFS_native','NFS_generated']:(b/name).mkdir(exist_ok=True)
print(json.dumps(dict(cache=str(c),imports=records,verified_export_files={len(pins)})))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 (E/f'NFS_SETUP-{retry}.log').write_text(r.stdout[:2000]+r.stderr)
 if r.returncode==0:
  data=r.stdout.splitlines()[-1].encode();(E/'NFS_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(data));break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 if r.returncode==78 and retry<10:time.sleep(180);continue
 if r.returncode==79 and retry==0:time.sleep(30);continue
 raise RuntimeError('STOP shared infrastructure: '+r.stderr+r.stdout)
else:raise RuntimeError('admission exhausted')
print('verified exports and copied',len(json.loads(data)['imports']),'cache inputs')
