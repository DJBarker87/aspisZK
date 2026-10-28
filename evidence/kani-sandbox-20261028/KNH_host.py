"""Own transport/admission wrapper; never modifies the shared launchers."""
from pathlib import Path
import subprocess,json,shlex,time,hashlib,zlib,base64
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-kani-sandbox-20261028'
def ssh(code,submitted=False):
 for trial in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],capture_output=True,text=True)
  with (E/'KNH_NATIVE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,submitted=submitted,command=code,stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),stdout_bytes=len(r.stdout.encode()),stdout_tail=r.stdout[-1500:],stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if trial<10:print('transport255; waiting60s',flush=True);time.sleep(60)
 raise SystemExit('STOP persistent transport255')
def py(code,submitted=False):return ssh('python3 -c '+shlex.quote(code),submitted)
def admit(a):
 for retry in range(11):
  r=py(f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text(),end='');sys.exit(r.returncode)
''')
  (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
  try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
  except (StopIteration,json.JSONDecodeError):
   if retry==0:time.sleep(30);continue
   raise SystemExit('STOP admission receipt absent')
  (E/(a+'-reservation.json')).write_text(json.dumps(ad,indent=2)+'\n')
  if r.returncode==0 and ad.get('allowed') is True:return retry
  if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('admission refusal; wait180s',flush=True);time.sleep(180);continue
  raise SystemExit('STOP admission error')
 raise SystemExit('STOP reservation exhausted')
def launch(cfg):
 assert not (E/cfg['attempt']/'receipt.json').exists()
 cfg['reservation_retries']=admit(cfg['attempt'])
 (E/(cfg['attempt']+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 r=py(f'''from pathlib import Path
import json
b=Path({B!r});cfg=json.loads({json.dumps(json.dumps(cfg))});p=b/(cfg['attempt']+'.json');assert not (b/cfg['attempt']).exists();p.write_text(json.dumps(cfg,indent=2)+'\\n')
''')
 assert r.returncode==0,r.stderr
 cmd='cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+shlex.quote(cfg['attempt']+'.json')
 r=ssh(cmd,submitted=True);(E/(cfg['attempt']+'-launcher.log')).write_text(r.stdout+r.stderr)
 # Recover read-only, including after submitted transport255; never resubmit.
 r=py(f'''from pathlib import Path
import json
b=Path({B!r})/{cfg['attempt']!r}
import base64,zlib
print(base64.b64encode(zlib.compress(json.dumps({{n:(b/n).read_text() for n in ['receipt.json','stdout.log','time.log'] if (b/n).is_file()}}).encode())).decode())
''')
 assert r.returncode==0,r.stderr
 out=json.loads(zlib.decompress(base64.b64decode(r.stdout)))
 for n,s in out.items():p=E/cfg['attempt']/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 if 'receipt.json' not in out:raise SystemExit('STOP missing receipt after submission; do not resubmit')
 rc=json.loads(out['receipt.json']);
 with (E/'KNH_ATTEMPTS.jsonl').open('a') as ledger:ledger.write(json.dumps(rc)+'\n')
 print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True);
 if cfg['kind']!='metadata':
  log=out['stdout.log'];pos=log.rfind('Checking harness');print(log[pos:] if pos>=0 and len(log)-pos<18000 else log[-3000:],flush=True)
 return rc
