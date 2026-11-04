"""Copy selected object variants; never modify predecessor caches or launchers."""
from pathlib import Path
import subprocess,json,lzma,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-prepare-20261104'
C='/home/dombarker/project-offloads/codex-cx-slice-d-prepare-cache-20261104'
roots=json.loads((E/'NFW_SEED_PATHS.json').read_text())
code=f'''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/'NFW_SETUP-admission.json'
with (b/'NFW_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode!=0 or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
c=Path({C!r});c.mkdir(exist_ok=True);records=[];selected={{}}
for root in {roots!r}:
 if not any(t in Path(root).name for t in ['exports','NFJ_objects','NCO_objects']):continue
 for p in sorted(Path(root).rglob('*.olean')):
  rel=str(p.relative_to(root))
  if rel not in selected:selected[rel]=p
need=sum(z.stat().st_size for p in selected.values() for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')] if z.is_file())
free=shutil.disk_usage(c).free
print(json.dumps(dict(copy_bytes=need,free_bytes=free)),flush=True)
if need+8*1024**3>free:sys.exit('STOP host disk headroom insufficient for private selected cache')
for rel,p in selected.items():
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  q=c/Path(rel).parent/z.name;q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copyfile(z,q)
  h=hashlib.sha256(z.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  records.append(dict(source=str(z),destination=str(q),sha256=h,bytes=q.stat().st_size))
w=b.parent/'codex-cx-sound-int2-20261025'
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:(b/name).write_bytes((w/name).read_bytes())
for name in ['NFW_objects','NFW_tmp','NFW_native','NFW_generated']:(b/name).mkdir(exist_ok=True)
(b/'NFW_CACHE_IMPORTS.json').write_text(json.dumps(records))
print(json.dumps(dict(cache=str(c),count=len(records),bytes=need)),flush=True)
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 (E/f'NFW_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 if r.returncode==78 and retry<10:time.sleep(180);continue
 if r.returncode==79 and retry==0:time.sleep(30);continue
 raise RuntimeError('STOP setup: '+r.stdout+r.stderr)
else:raise RuntimeError('admission exhausted')
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/NFW_CACHE_IMPORTS.json'],text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NFW_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(r.stdout.encode()))
import hashlib
(E/'NFW_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(r.stdout.encode()).hexdigest()+'\n')
print((E/f'NFW_SETUP-{retry}.log').read_text()[-2000:])
