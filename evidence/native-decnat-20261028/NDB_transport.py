from pathlib import Path
import subprocess,json,time,shlex,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-native-decnat-20261028'
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def ssh(code,stdin=None,submitted=False):
 for trial in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NDB_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if trial<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
def py(code,**kw):return ssh('python3',stdin=code,**kw)
def admit(a):
 for trial in range(11):
  r=py(f'''from pathlib import Path
import subprocess,json
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/{(a+'-barrier-'+str(trial)+'.log')!r};q=b/{(a+'-reservation.json')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
print(json.dumps(dict(exit=r.returncode,log=p.read_text(),reservation=json.loads(q.read_text()) if q.exists() else None)))
''')
  assert r.returncode==0,r.stderr
  x=json.loads(r.stdout);(E/(a+f'-admission-{trial}.json')).write_text(json.dumps(x,indent=2)+'\n')
  if x['reservation'] is None:
   if trial==0:time.sleep(30);continue
   raise SystemExit('STOP infrastructure: missing reservation JSON')
  if x['exit']==0 and x['reservation'].get('allowed') is True:return
  if (x['exit']==78 or x['reservation'].get('allowed') is False) and trial<10:time.sleep(180);continue
  raise SystemExit('STOP infrastructure: admission failure '+str(x))
 raise SystemExit('STOP admission retries exhausted')
def upload(files):
 r=py('from pathlib import Path\nimport json\nb=Path('+repr(B)+')\nfor n,s in json.loads('+repr(json.dumps(files))+').items():\n p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)\n')
 assert r.returncode==0,r.stdout+r.stderr
