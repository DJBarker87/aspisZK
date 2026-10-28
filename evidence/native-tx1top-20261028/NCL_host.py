"""Own transport runner; unchanged S2H admission and S2W scope backend."""
from pathlib import Path
import subprocess,json,shlex,time,sys,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx1top-20261028'
def ssh(code,submitted=False):
 for trial in range(10):
  start=time.monotonic()
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],text=True,capture_output=True)
  with (E/'NCL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,submitted=submitted,stderr=r.stderr,wall_seconds=time.monotonic()-start))+'\n')
  if r.returncode!=255 or submitted:return r
  if trial<9:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
def remote_py(code,submitted=False):return ssh('python3 -c '+shlex.quote(code),submitted)
def admit(a):
 for retry in range(11):
  r=remote_py(f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text(),end='');sys.exit(r.returncode)
''')
  (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
  ad=next((json.loads(l) for l in r.stdout.splitlines() if l.startswith('{')),None)
  if ad is None:
   if retry==0:time.sleep(30);continue
   raise SystemExit('STOP missing admission JSON')
  (E/(a+'-reservation.json')).write_text(json.dumps(ad,indent=2)+'\n')
  if r.returncode==0 and ad.get('allowed') is True:return retry
  if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('wait180s admission',flush=True);time.sleep(180);continue
  raise SystemExit('STOP admission failure')
 raise SystemExit('STOP admission exhausted')
def collect_code(a):
 names=[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph.json',a+'-metadata.stderr',a+'-launcher.log',a+'-reservation.json',a+'-barrier.log']
 return f'''from pathlib import Path
import json
b=Path({B!r});names={names!r}
names += [str(p.relative_to(b)) for p in (b/{a!r}/'sources').rglob('*') if p.is_file()]
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file()}}))'''
def retain(raw):
 out=json.loads(raw)
 for n,data in out.items():
  p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(data)
 return out
def recover(a):
 r=remote_py(collect_code(a));assert r.returncode==0,r.stderr;retain(r.stdout)
 assert (E/a/'receipt.json').exists(),'STOP unresolved submitted run; never resubmit'
 return json.loads((E/a/'receipt.json').read_text())
if __name__=='__main__':
 if (E/'NCL_PAUSE').exists():raise SystemExit('paused before admission; no launch')
 a=sys.argv[1];assert a.startswith('NCL_K') and not (E/a/'receipt.json').exists()
 assert not (E/'NCL_ACTIVE.json').exists(),'STOP active Lean wrapper'
 assert len(list(E.glob('NCL_K[0-9][0-9][0-9]/receipt.json')))<50
 cfg=json.loads((E/(a+'.json')).read_text());cfg['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();cfg['source_tree_dirty']=True
 # A single transport serializes admission, own config, one scope and receipts.
 code=f'''from pathlib import Path
import subprocess,json,sys,re
b=Path({B!r});a={a!r};cfg=json.loads({json.dumps(cfg)!r})
assert not (b/a/'receipt.json').exists(),'existing terminal run'
rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
live=[x for x in rows if re.match(r'^(?:/usr/bin/)?python3 S2W_(?:run|lean)_host[.]py NCL_',x.strip())]
assert not live,live
with (b/(a+'-barrier.log')).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/(a+'-reservation.json'))],stdout=f,stderr=subprocess.STDOUT)
p=b/(a+'-reservation.json')
ad=json.loads(p.read_text()) if p.exists() else None
if r.returncode!=0 or not ad or ad.get('allowed') is not True:
 print(json.dumps(dict(admission=ad,admission_exit=r.returncode,barrier=(b/(a+'-barrier.log')).read_text())));sys.exit(78 if (r.returncode==78 or (ad and ad.get('allowed') is False)) else 79)
(b/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\\n')
with (b/(a+'-launcher.log')).open('w') as f:r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','S2W_run_host.py',a+'.json'],cwd=b,stdout=f,stderr=subprocess.STDOUT)
{collect_code(a)}
'''
 for retry in range(11):
  r=remote_py(code,submitted=True)
  if r.returncode==255:
   # Submission status is ambiguous: recover only; never repeat this payload.
   time.sleep(60);rc=recover(a);break
  if r.returncode in [78,79]:
   (E/(a+f'-admission-refusal-{retry}.json')).write_text(r.stdout+r.stderr)
   ad=json.loads(r.stdout)
   if r.returncode==79:
    if ad.get('admission') is None and retry==0:time.sleep(30);continue
    raise SystemExit('STOP infrastructure admission failure: '+r.stdout+r.stderr)
   if retry<10:print('admission refused; wait180s',flush=True);time.sleep(180);continue
   raise SystemExit('STOP admission retries exhausted')
  assert r.returncode==0,r.stdout+r.stderr
  retain(r.stdout)
  if not (E/a/'receipt.json').exists():raise SystemExit('STOP no terminal scope receipt; recover read-only')
  rc=json.loads((E/a/'receipt.json').read_text());break
 else:raise SystemExit('STOP no admission')
 with (E/'NCL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
 print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
 print('\n'.join(l for l in (E/a/'stdout.log').read_text().splitlines() if l.startswith(('VERIFICATION','Checking harness','error:','error[')) or 'kani_exit' in l),flush=True)
