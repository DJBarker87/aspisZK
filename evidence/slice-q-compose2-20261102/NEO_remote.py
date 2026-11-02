"""Lane-owned transport and admission clients, no host infrastructure changes."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-slice-q-compose2-20261102'
I='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
def ssh(attempt,command,stdin=None,submitted=False):
 for k in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,command],input=stdin,text=True,capture_output=True)
  with (E/'NEO_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=attempt,try_number=k,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if k<10:time.sleep(60)
 raise RuntimeError('STOP persistent transport failure')
def admit(a):
 for k in range(11):
  code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});log=b/{(a+'-barrier-'+str(k)+'.log')!r};receipt=b/{(a+'-admission.json')!r}
with log.open('w') as f:r=subprocess.run(['python3',{I!r}+'/JFz_reservation.py',str(receipt)],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text());sys.exit(r.returncode)
'''
  r=ssh(a,'python3',code);(E/f'{a}-barrier-{k}.log').write_text(r.stdout+r.stderr)
  try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
  except (StopIteration,json.JSONDecodeError):
   if k==0:time.sleep(30);continue
   raise RuntimeError('STOP infrastructure: missing reservation JSON')
  (E/f'{a}-admission.json').write_text(json.dumps(dict(exit_status=r.returncode,reservation=ad),indent=1)+'\n')
  if r.returncode==0 and ad.get('allowed') is True:return ad
  if (r.returncode==78 or ad.get('allowed') is False) and k<10:time.sleep(180);continue
  raise RuntimeError('STOP infrastructure: admission failed')
 raise RuntimeError('STOP reservation retry exhaustion')
def upload(a,files):
 r=ssh(a,'python3',f'''from pathlib import Path
import json
b=Path({B!r})
for name,source in json.loads({json.dumps(files)!r}).items():
 p=b/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(source)
''');assert r.returncode==0,r.stderr
