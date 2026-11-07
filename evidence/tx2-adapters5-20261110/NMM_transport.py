"""Owned orchestration only; shared admission and launchers are unchanged."""
from pathlib import Path
import json, subprocess, time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx2-adapters5-20261110'
H='dombarker@100.108.41.90'
def ssh(code, data=None, submitted=False):
    for retry in range(11):
        r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
        with (E/'NMM_TRANSPORT.jsonl').open('a') as f:
            f.write(json.dumps(dict(retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
        if r.returncode!=255:return r
        if submitted:raise RuntimeError('Submitted transport lost: recover read-only, NEVER resubmit')
        if retry<10:time.sleep(60)
    raise RuntimeError('Transport exhausted')
def admission(a, scope=True):
    while scope:
        count = ssh('python3', """import subprocess,pathlib,json
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True).splitlines();active=[]
for line in units:
 unit=line.split()[0]
 if unit=='init.scope':continue
 cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip()
 root=pathlib.Path('/sys/fs/cgroup'+cg);hits=[]
 for procs in root.rglob('cgroup.procs'):
  try:pids=procs.read_text().split()
  except OSError:continue
  for pid in pids:
   try:
    proc=pathlib.Path('/proc')/pid;cwd=str((proc/'cwd').resolve());argv=(proc/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
    if '/home/dombarker/project-offloads/codex-cx-' in cwd or '/home/dombarker/project-offloads/codex-cx-' in argv:hits.append(dict(pid=pid,cwd=cwd,argv=argv))
   except OSError:pass
 if hits:active.append(dict(unit=unit,processes=hits))
print(json.dumps(dict(count=len(active),scopes=active)))
""")
        assert count.returncode==0, 'Stream A count probe failed'
        current=json.loads(count.stdout)
        with (E/'NMM_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,kind='wait' if current['count']>=2 else 'share_check',probe=current))+'\n')
        if current['count']<2:break
        for _ in range(3):time.sleep(60)
    for disk_retry in range(7):
        disk=ssh('python3',"import shutil,json;print(json.dumps(dict(free_bytes=shutil.disk_usage('/').free)))")
        assert disk.returncode==0, 'Host disk probe failed'
        free=json.loads(disk.stdout)['free_bytes']
        (E/(a+f'-disk-{disk_retry}.json')).write_text(json.dumps(dict(free_bytes=free,minimum_bytes=40_000_000_000,allowed=free>=40_000_000_000))+'\n')
        if free>=40_000_000_000:break
        if disk_retry==6:raise RuntimeError('STOP: disk below40GB after6 waits')
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
        if (r.returncode==78 or ad.get('allowed') is False) and retry<10:[time.sleep(60) for _ in range(3)];continue
        raise RuntimeError('Infrastructure STOP: admission')
