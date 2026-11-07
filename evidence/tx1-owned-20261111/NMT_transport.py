"""Owned orchestration only; shared admission and launchers are unchanged."""
from pathlib import Path
import json, subprocess, time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx1-owned-20261111'
H='dombarker@100.108.41.90'
def ssh(code, data=None, submitted=False):
    for retry in range(11):
        r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
        with (E/'NMT_TRANSPORT.jsonl').open('a') as f:
            f.write(json.dumps(dict(retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
        if r.returncode!=255:return r
        if submitted:raise RuntimeError('Submitted transport lost: recover read-only, NEVER resubmit')
        if retry<10:time.sleep(60)
    raise RuntimeError('Transport exhausted')
def admission(a):
    share(a)
    for disk_retry in range(7):
        r=ssh("python3", "import shutil,json;print(json.dumps({'free_bytes':shutil.disk_usage('/home/dombarker/project-offloads').free}))")
        assert r.returncode==0,r.stderr
        disk=json.loads(r.stdout)
        with (E/'NMT_DISK.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=disk_retry,**disk))+'\n')
        if disk['free_bytes']>=40_000_000_000:break
        if disk_retry==6:raise RuntimeError('STOP host disk below 40 GB after six waits')
        for _ in range(10):time.sleep(60)

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

def share(a):
    while True:
        r=ssh('python3', """import subprocess,json,pathlib
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True).splitlines();found=[]
for line in units:
 u=line.split()[0];g=subprocess.check_output(['systemctl','--user','show',u,'--property=ControlGroup','--value'],text=True).strip();p=pathlib.Path('/sys/fs/cgroup'+g)
 matched=[]
 for f in p.rglob('cgroup.procs'):
  try:pids=f.read_text().split()
  except OSError as error:
   if error.errno!=95:raise
   pids=f.with_name('cgroup.threads').read_text().split()
  for pid in pids:
   try:
    cwd=str(pathlib.Path('/proc',pid,'cwd').resolve(strict=True))
    if cwd.startswith('/home/dombarker/project-offloads/codex-'):matched.append({'pid':pid,'cwd':cwd})
   except (OSError,FileNotFoundError):pass
 if matched:found.append({'unit':u,'processes':matched})
print(json.dumps({'scopes':found,'count':len(found)}))""")
        assert r.returncode==0,r.stderr
        x=json.loads(r.stdout)
        with (E/'NMT_SHARE.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,**x))+'\n')
        if x['count']<6:return
        with (E/'NMT_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,kind='wait',reason='host share',count=x['count']))+'\n')
        for _ in range(3):time.sleep(60)
