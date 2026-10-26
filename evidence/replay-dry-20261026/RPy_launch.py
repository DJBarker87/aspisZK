"""Job-specific serial orchestration of unchanged admission and run launchers."""
from pathlib import Path
import json,subprocess,time,sys
E=Path(__file__).resolve().parent; H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-replay-dry-20261026'
def ssh(cmd):return subprocess.run(['ssh',H,cmd],text=True,capture_output=True)
def collect(name):
 r=subprocess.run(['scp','-q',H+':'+B+'/'+name,str(E/name)],capture_output=True,text=True)
 if r.returncode:raise SystemExit('STOP collection: '+r.stderr)
collect('RPy_source-manifest.json'); rows=json.loads((E/'RPy_source-manifest.json').read_text());failed=set()
for row in rows:
 a=row['attempt'];i=int(a.split('_')[1])
 if i < int(sys.argv[1]):continue
 if any(m in failed for m in row['imports']):
  failed.add(row['module']);(E/(a+'-blocked.json')).write_text(json.dumps({'module':row['module'],'status':'blocked by failed dependency','imports':row['imports']})+'\n');continue
 for retry in range(11):
  reservation=f'{B}/{a}-reservation.json'; barrier=f'{B}/{a}-barrier-{retry}.log'
  r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {reservation} > {barrier} 2>&1')
  collect(a+f'-barrier-{retry}.log')
  exists=ssh(f'test -f {reservation}').returncode==0
  if not exists and retry==0:time.sleep(30);continue
  if r.returncode==0:collect(a+'-reservation.json');break
  if r.returncode==78 and retry<10:time.sleep(180);continue
  log=(E/(a+f'-barrier-{retry}.log')).read_text()
  if 'FileNotFoundError' in log and retry==0:time.sleep(30);continue
  raise SystemExit('STOP admission: '+log)
 else:raise SystemExit('STOP admission exhausted')
 # Pin direct predecessor artifacts; no existing cached object is eligible.
 pin="""import json,hashlib
from pathlib import Path
B=Path('%s');a='%s';m=json.loads((B/'RPy_source-manifest.json').read_text())[%d];p=B/(a+'.json');c=json.loads(p.read_text());objs={}
for n in m['imports']:
 q=B/(n.replace('.','/')+'.olean');assert q.is_file(),str(q);objs[n]={'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size}
c['deps_fingerprint']['selected_objects']=objs;p.write_text(json.dumps(c,indent=2)+'\\n')
"""%(B,a,i-1)
  # Metadata only: no compiler/build launcher is implemented here.
 r=subprocess.run(['ssh',H,'python3 -'],input=pin,text=True,capture_output=True)
 if r.returncode:raise SystemExit('STOP dependency pin: '+r.stderr)
 collect(a+'.json')
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 (E/a).mkdir(exist_ok=True)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 receipt=json.loads((E/a/'receipt.json').read_text())
 print(a,row['module'],'exit',receipt['exit_status'],'wall',round(receipt['wall_seconds'],2),'rss',receipt['peak_rss_kib'],flush=True)
 if receipt['exit_status']!=0:failed.add(row['module'])
 # No failed target is retried. Independent modules can still use the budget.
