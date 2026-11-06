from pathlib import Path
import subprocess,json,hashlib,sys,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-pair8-20261107'
P='/home/dombarker/project-offloads/codex-cx-slice-d-pair7-20261107'
H='dombarker@100.108.41.90'
def ssh(code):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
  with (E/'NJF_SEED_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport retries exhausted')
for retry in range(11):
 r=ssh(f"""from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/'NJF_SEED-admission.json'
with (b/'NJF_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
""")
 (E/f'NJF_SEED-barrier-{retry}.log').write_text(r.stdout+r.stderr)
 try:a=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('Missing reservation JSON')
 (E/'NJF_SEED-admission.json').write_text(json.dumps(dict(exit=r.returncode,reservation=a)))
 if r.returncode==0 and a.get('allowed') is True:break
 if (r.returncode==78 or a.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise RuntimeError('Admission denied')
r=ssh(f"""from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});s=Path({P!r});assert json.loads((b/'NJF_SEED-admission.json').read_text())['allowed'] is True
assert shutil.disk_usage(b).free>2000000000
files={{}}
for old,new in [('NIW_objects','NJF_seed/objects'),('NIW_seed','NJF_seed/base'),('NIW_native','NJF_seed/native')]:
 src=s/old;dst=b/new
 assert not dst.exists(),str(dst)
 shutil.copytree(src,dst)
 for p in dst.rglob('*'):
  if p.is_file():files[str(p.relative_to(b))]={{'source':str(src/p.relative_to(dst)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}}
for name in ['S2W_run_host.py','S2W_lean_host.py']:
 shutil.copy2(s/name,b/name)
for name in ['NJF_objects','NJF_native','NJF_tmp','NJF_target']:(b/name).mkdir(exist_ok=True)
print(json.dumps(dict(source=str(s),workspace=str(b),CARGO_TARGET_DIR=str(b/'NJF_target'),files=files,seed_bytes=sum(x['bytes'] for x in files.values()),free_after=shutil.disk_usage(b).free)))
""")
assert r.returncode==0,r.stderr
(E/'NJF_SEED.json').write_text(r.stdout)
x=json.loads(r.stdout);print(json.dumps(dict(seed_bytes=x['seed_bytes'],files=len(x['files']),free_after=x['free_after'])))
