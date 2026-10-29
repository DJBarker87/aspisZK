"""Serial task transport using the unchanged lead-owned S2W runner."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,re,shlex
E=Path(__file__).resolve().parent;R=E.parents[1];B='/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028';H='dombarker@100.108.41.90';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,m=sys.argv[1:];assert re.fullmatch(r'NDR_L\d{3}',a);assert m.startswith(('NDO_', 'NDR_'))
assert len(list(E.glob('NDR_L[0-9][0-9][0-9].json')))<60
assert not (E/(a+'.json')).exists(),'attempt already reserved; recover only'
src=R/'lean'/(m+'.lean');assert src.is_file()
def ledger(row):
 with (E/'NDR_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
def ssh(cmd,submitted=False):
 for n in range(11):
  p=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,cmd],capture_output=True,text=True)
  if p.returncode!=255:return p
  ledger(dict(kind='transport',attempt=a,retry=n,submitted=submitted,exit_status=p.returncode,stderr=p.stderr))
  if submitted:raise RuntimeError('submitted transport failed; recover read-only; NEVER resubmit')
  if n<10:time.sleep(60)
 raise RuntimeError('transport exhausted')
def get(n):
 p=ssh('cat '+shlex.quote(B+'/'+n));assert p.returncode==0,p.stderr
 dst=E/n;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(p.stdout);return p.stdout
for retry in range(11):
 p=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier-{retry}.log 2>&1')
 get(a+f'-barrier-{retry}.log')
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if exists:ad=json.loads(get(a+'-reservation.json'))
 else:ad={}
 allowed=p.returncode==0 and ad.get('allowed') is True
 ledger(dict(kind='admission',attempt=a,retry=retry,exit_status=p.returncode,allowed=allowed))
 if allowed:break
 if not exists and retry==0:time.sleep(30);continue
 if p.returncode==78 or ad.get('allowed') is False:
  assert retry<10,'admission exhausted'
  print('contention; wait 180 seconds',flush=True);time.sleep(180);continue
 raise RuntimeError('host admission infrastructure failure '+p.stderr)
# Fingerprint direct imports, with immutable full copied-closure manifest pin.
deps=[n for s in re.findall(r'^import\s+([^\n]+)',src.read_text(),re.M) for n in s.split()]
code='from pathlib import Path;import json,hashlib;b=Path('+repr(B)+');names='+repr(deps)+';print(json.dumps({n:{"path":str(b/"objects"/(n.replace(".","/")+".olean")),"sha256":hashlib.sha256((b/"objects"/(n.replace(".","/")+".olean")).read_bytes()).hexdigest()} for n in names}))'
p=ssh('python3 -c '+shlex.quote(code));assert p.returncode==0,p.stderr
objects=json.loads(p.stdout)
cfg=dict(kind='lean',module=m,attempt=a,sources=[m+'.lean'],env={'LEAN_PATH':B+'/objects:'+T+'/lib/lean'},timeout=180,command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','objects/'+m+'.olean',m+'.lean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=R).strip(),source_tree_dirty=True,deps_fingerprint=dict(scope='Copied immutable headline closure plus unaffected witness modules; imports only retarget; seed manifest pinned',seed_manifest_sha256=hashlib.sha256((E.parent/'native-reconcile-20261028/NDO_SEED_PINS.json').read_bytes()).hexdigest(),selected_objects=objects),expected_time='single module import and symbolic re-elaboration; no new arithmetic certificate generation',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
p=subprocess.run(['scp','-q','-o','ControlMaster=no',str(E/(a+'.json')),str(src),H+':'+B+'/'],capture_output=True,text=True);assert p.returncode==0,p.stderr
p=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json',submitted=True)
(E/(a+'-launcher.log')).write_text(p.stdout+p.stderr)
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
r=json.loads((E/a/'receipt.json').read_text());ledger(r);print(json.dumps({k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-4500:])
