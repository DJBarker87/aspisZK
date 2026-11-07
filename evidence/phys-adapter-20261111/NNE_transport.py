"""Owned orchestration only; shared admission and launchers are unchanged."""
from pathlib import Path
import json, subprocess, time, lzma, hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-phys-adapter-20261111'
H='dombarker@100.108.41.90'
def ssh(code, data=None, submitted=False):
    for retry in range(11):
        r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
        with (E/'NNE_TRANSPORT.jsonl').open('a') as f:
            f.write(json.dumps(dict(retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
        if r.returncode!=255:return r
        if submitted:raise RuntimeError('Submitted transport lost: recover read-only, NEVER resubmit')
        if retry<10:time.sleep(60)
    raise RuntimeError('Transport exhausted')
def admission(a):
    while True:
        r=ssh('python3', """import subprocess,pathlib,json
names=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True).splitlines()
active=[];owned=[]
for line in names:
 unit=line.split()[0]
 cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip()
 root=pathlib.Path('/sys/fs/cgroup')/cg.lstrip('/')
 hit=False;own=False
 for f in root.rglob('cgroup.procs'):
  for pid in f.read_text().split():
   try:
    cwd=str(pathlib.Path('/proc',pid,'cwd').resolve());hit |= cwd.startswith('/home/dombarker/project-offloads/codex-');own |= cwd=='/home/dombarker/project-offloads/codex-cx-phys-adapter-20261111'
   except OSError:pass
 if hit:active.append(unit)
 if own:owned.append(unit)
print(json.dumps({'stream_a_scopes':active,'count':len(active),'owned_scopes':owned}))
""")
        assert r.returncode==0,r.stderr
        share=json.loads(r.stdout)
        with (E/'NNE_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(kind='wait' if (share['count']>=6 or share['owned_scopes']) else 'share_check',attempt=a,**share))+'\n')
        if share['count']<6 and not share['owned_scopes']:break
        print(json.dumps(dict(attempt=a,status='wait',reason='Stream A saturation',**share)),flush=True)
        for _ in range(3):time.sleep(60)
    for disk_retry in range(7):
        r=ssh("python3", "import shutil,json;print(json.dumps({'free_bytes':shutil.disk_usage('/home/dombarker/project-offloads').free}))")
        assert r.returncode==0,r.stderr
        disk=json.loads(r.stdout)
        with (E/'NNE_DISK.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=disk_retry,**disk))+'\n')
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
        raw=(r.stdout+r.stderr).encode();(E/(a+f'-barrier-{retry}.log.xz')).write_bytes(lzma.compress(raw));(E/(a+f'-barrier-{retry}.log.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
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
