"""Owned orchestration only; shared admission and launchers are unchanged."""
from pathlib import Path
import json, subprocess, time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-root0-weak-20261111'
H='dombarker@100.108.41.90'
def ssh(code, data=None, submitted=False):
    for retry in range(11):
        r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
        with (E/'NNC_TRANSPORT.jsonl').open('a') as f:
            f.write(json.dumps(dict(retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
        if r.returncode!=255:return r
        if submitted:raise RuntimeError('Submitted transport lost: recover read-only, NEVER resubmit')
        if retry<10:time.sleep(60)
    raise RuntimeError('Transport exhausted')
def admission(a):
    for disk_retry in range(7):
        r=ssh("python3", "import shutil,json;print(json.dumps({'free_bytes':shutil.disk_usage('/home/dombarker/project-offloads').free}))")
        assert r.returncode==0,r.stderr
        disk=json.loads(r.stdout)
        with (E/'NNC_DISK.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=disk_retry,**disk))+'\n')
        if disk['free_bytes']>=40_000_000_000:break
        if disk_retry==6:raise RuntimeError('STOP host disk below 40 GB after six waits')
        for _ in range(10):time.sleep(60)

    while True:
        r=ssh('python3',"""import subprocess,json,pathlib
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True)
active=[]
for line in units.splitlines():
 u=line.split()[0]
 cg=subprocess.check_output(['systemctl','--user','show',u,'-p','ControlGroup','--value'],text=True).strip()
 base=pathlib.Path('/sys/fs/cgroup'+cg)
 found=False
 for procs in base.rglob('cgroup.procs'):
  try:members=procs.read_text()
  except OSError as error:
   if error.errno!=95:raise
   members=(procs.parent/'cgroup.threads').read_text()
  for pid in members.split():
   try:cwd=str(pathlib.Path('/proc',pid,'cwd').resolve(strict=True))
   except (OSError,RuntimeError):continue
   if cwd.startswith('/home/dombarker/project-offloads/codex-'):found=True
 if found:active.append(u)
print(json.dumps({'scopes':active,'count':len(active)}))""")
        assert r.returncode==0,r.stderr
        share=json.loads(r.stdout)
        with (E/'NNC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,kind='share_check' if share['count']<6 else 'wait',**share))+'\n')
        if share['count']<6:break
        for _ in range(3):time.sleep(60)
    for retry in range(11):
        r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True);p=b/{(a+'-reservation.json')!r}
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
        (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
        try:ad=json.loads(r.stdout)
        except json.JSONDecodeError:
            if retry==0:time.sleep(30);continue
            raise RuntimeError('Infrastructure STOP: missing admission')
        (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad),indent=1)+'\n')
        if r.returncode==0 and ad.get('allowed') is True:return
        if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
            for _ in range(3):time.sleep(60)
            continue
        raise RuntimeError('Infrastructure STOP: admission')
