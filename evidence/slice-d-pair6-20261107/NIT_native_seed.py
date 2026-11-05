from pathlib import Path
import subprocess,json,time,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-d-pair6-20261107'
def ssh(code):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
  with (E/'NIT_NATIVE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if retry<10:time.sleep(60)
 raise RuntimeError('ten transport retries exhausted before any proof launch')
for retry in range(11):
 r=ssh(f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});p=b/'NIT_NATIVE-admission.json'
with (b/'NIT_NATIVE-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/f'NIT_NATIVE-barrier-{retry}.log').write_text(r.stdout+r.stderr)
 try:a=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('Missing admission receipt after retry')
 if r.returncode==0 and a.get('allowed') is True:break
 if (r.returncode==78 or a.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise RuntimeError('Admission failed')
r=ssh(f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});s=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair4-20261107/NIG_src');d=b/'NIT_src'
a=json.loads((b/'NIT_NATIVE-admission.json').read_text());assert a['allowed'] is True
free_before=shutil.disk_usage(b).free;assert free_before>1500000000
shutil.copytree(s,d,dirs_exist_ok=True,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
files={{str(p.relative_to(d)):{{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}} for p in d.rglob('*') if p.is_file()}}
print(json.dumps(dict(admission=a,source=str(s),bytes=sum(v['bytes'] for v in files.values()),files=files,free_before=free_before,free_after=shutil.disk_usage(b).free)))
''');assert r.returncode==0,r.stderr
(E/'NIT_NATIVE_SEED.json').write_text(r.stdout);x=json.loads(r.stdout);print(json.dumps({'seed_bytes':x['bytes'],'files':len(x['files']),'free_after':x['free_after']}))
