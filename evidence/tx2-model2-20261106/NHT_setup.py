from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx2-model2-20261106'
C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHT_seed_20261106'
old=json.loads((E.parent/'tx2-model-20261106/NHQ_PATHS.json').read_text())
roots=['/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHR_exports_20261106','/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHQ_exports_20261106','/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104/NGK_exports_20261105']
code=f'''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path({B!r});b.mkdir(exist_ok=True); p=b/'NHT_SETUP-admission.json'
with (b/'NHT_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode!=0 or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
c=Path({C!r});c.mkdir(exist_ok=True);records=[]
for root in map(Path,{roots!r}):
 assert root.is_dir(),str(root)
 for z in sorted(root.rglob('*')):
  if not z.is_file() or not any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  q=c/z.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copyfile(z,q)
  h=hashlib.sha256(z.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  records.append(dict(source=str(z),destination=str(q),sha256=h,bytes=q.stat().st_size))
w=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:(b/n).write_bytes((w/n).read_bytes())
for n in ['NHT_objects','NHT_generated','NHT_native','NHT_tmp']:(b/n).mkdir(exist_ok=True)
pins=dict(files=records,total_bytes=sum(x['bytes'] for x in records),disk_free=shutil.disk_usage(c).free)
(b/'NHT_SEED.json').write_text(json.dumps(pins));print('NHT_SEED '+json.dumps(pins))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 (E/f'NHT_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 if r.returncode==78 and retry<10:time.sleep(180);continue
 if r.returncode==79 and retry==0:time.sleep(30);continue
 raise RuntimeError(r.stdout+r.stderr)
seed=json.loads(next(x.removeprefix('NHT_SEED ') for x in r.stdout.splitlines() if x.startswith('NHT_SEED ')))
(E/'NHT_SEED.json').write_text(json.dumps(seed,indent=1)+'\n')
paths=[B+'/NHT_objects',C,C+'/objects',*old]
paths += ['/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104/NHI_exports_20261106/objects','/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104/NHE_exports_20261106/objects']
(E/'NHT_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
print(json.dumps(dict(seed_bytes=seed['total_bytes'],files=len(seed['files']),disk_free=seed['disk_free'])))
