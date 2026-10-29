"""Serial lane-owned validation wrapper; host launcher is copied unchanged."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose-20261029';H='dombarker@100.108.41.90'
a,target=sys.argv[1:];assert a.startswith('NED_L') and 1<=int(a[5:])<=150
assert not (E/a).exists();active=E/'NED_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NED_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP infrastructure: reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise SystemExit('STOP infrastructure admission')
local=E/(target+'.lean')
imported=E/'NED_imports'/(target+'.lean')
source=local.read_text() if local.exists() else imported.read_text() if imported.exists() else json.loads((E/'NED_UNCHANGED_BUILD_PLAN.json').read_text())['sources'][target]['source']
# Dependency pinning resolves the exact LEAN_PATH order, including the Aeneas library.
code=f'''from pathlib import Path
import re,json,hashlib
b=Path({B!r});coherent=b.parent/'codex-cx-sound-int2-20261025'
roots=[b/'NED_objects',b.parent/'codex-cx-slice-s-compose-cache-20261029/NDM_front4b_objects_20261029',b.parent/'codex-cx-slice-s-compose-cache-20261029',coherent,coherent/'objects']
selected={{}};missing=[];seen=set()
def visit(n):
 if n in seen:return
 seen.add(n);rel=n.replace('.','/')
 p=next((r/(rel+'.olean') for r in roots if (r/(rel+'.olean')).exists()),None)
 if p is None:missing.append(n);return
 selected[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 q=next((r/(rel+'.lean') for r in [b/'NED_generated',*roots] if (r/(rel+'.lean')).exists()),None)
 if q:
  for dep in re.findall(r'^import\\s+([\\w.]+)',q.read_text(),re.M):visit(dep)
for n in re.findall(r'^import\\s+([\\w.]+)',{source!r},re.M):visit(n)
for p in [coherent/'objects/Aeneas.olean',*(coherent/'objects/Aeneas').rglob('*.olean')]:selected[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(dict(selected_objects=selected,missing=missing)))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr;pins=json.loads(r.stdout)
(E/(a+'-pins.json')).write_text(json.dumps(pins,indent=1)+'\n')
if pins['missing']:active.unlink();raise SystemExit('Missing unchanged dependencies: '+str(pins['missing']))
command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NED_generated','-o','NED_objects/'+target+'.olean','NED_generated/'+target+'.lean']
cfg=dict(attempt=a,kind='lean',module=target,sources=['NED_generated/'+target+'.lean'],command=command,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',LEAN_PATH=B+'/NED_objects:/home/dombarker/project-offloads/codex-cx-slice-s-compose-cache-20261029/NDM_front4b_objects_20261029:/home/dombarker/project-offloads/codex-cx-slice-s-compose-cache-20261029:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=pins)
(E/a).mkdir();(E/a/'NED_SOURCE.lean.txt').write_text(source)
files={'NED_generated/'+target+'.lean':source,a+'.json':json.dumps(cfg)}
code=f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
# Recovery is read-only even after a transport failure; never submit twice.
code=f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log']!r} if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr;out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'unresolved submitted attempt; never resubmit'
rc=json.loads(out[a+'/receipt.json']);
entry={k:v for k,v in rc.items() if k!='deps_fingerprint'}
entry['full_receipt']=dict(path=str(E/a/'receipt.json'),sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest())
with (E/'NED_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
active.unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-2000:] if rc['exit_status'] else '')

sys.exit(rc["exit_status"])
