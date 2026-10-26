"""Serial job orchestration of unchanged reservation and S2W command runner."""
from pathlib import Path
import json,subprocess,time,sys
E=Path(__file__).resolve().parent; H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-replay-dry-20261026'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
def ssh(cmd):return subprocess.run(['ssh',H,cmd],text=True,capture_output=True)
def collect(name):
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['scp','-q',H+':'+B+'/'+name,str(p)],capture_output=True,text=True)
 if r.returncode:raise SystemExit('STOP collection: '+r.stderr)
collect('RPz_inputs.json');rows=json.loads((E/'RPz_inputs.json').read_text());plan=json.loads((E/'RPz_source-plan.json').read_text())
state={};attempt=0;blocked=[]
for row in rows:
 m=row['module'];missing=[n for n in row['imports'] if plan['modules'][n]['kind']!='trusted-library' and state.get(n)!='passed']
 if missing:
  state[m]='blocked';blocked.append({'module':m,'missing':missing});continue
 if attempt>=599:break
 attempt+=1;a=f'RPz_{attempt:03d}'
 if (E/a/'receipt.json').exists():
  receipt=json.loads((E/a/'receipt.json').read_text());assert receipt['module']==m
  state[m]='passed' if receipt['exit_status']==0 else 'failed';continue
 for retry in range(11):
  reservation=f'{B}/{a}-reservation.json';barrier=f'{B}/{a}-barrier-{retry}.log'
  r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {reservation} > {barrier} 2>&1')
  collect(a+f'-barrier-{retry}.log')
  exists=ssh(f'test -f {reservation}').returncode==0
  if not exists and retry==0:time.sleep(30);continue
  if r.returncode==0:collect(a+'-reservation.json');break
  if r.returncode==78 and retry<10:
   print(a,'reservation contention; waiting 180s',flush=True);time.sleep(180);continue
  log=(E/(a+f'-barrier-{retry}.log')).read_text()
  if 'FileNotFoundError' in log and retry==0:time.sleep(30);continue
  raise SystemExit('STOP admission: '+log)
 else:raise SystemExit('STOP admission retries exhausted')
 cfg=dict(kind='lean',module=m,env={'LEAN_PATH':T+'/lib/lean:'+B+'/RPz_objects:'+B+'/RPz_trusted'},timeout=540,command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','RPz_sources','-o',row['object'],row['source']],sources=[row['source']],attempt=a,source_revision=plan['revision'],source_tree_dirty=False,deps_fingerprint={'scope':'fresh repository closure; release-pinned toolchain/library objects only','toolchain':'leanprover/lean4:v4.32.0'},expected_time='one committed repository module elaboration and kernel checking; no generated arithmetic probe',repository_source=row['repository_source'],reservation_retries=retry)
 # Pin actual direct predecessors before calling the existing runner.
 payload="""import json,hashlib
from pathlib import Path
B=Path(%r);T=Path(%r);row=json.loads(%r);cfg=json.loads(%r);objs={}
for n in row['imports']:
 ps=[T/'lib/lean'/(n.replace('.','/')+'.olean'),B/'RPz_objects'/(n.replace('.','/')+'.olean'),B/'RPz_trusted'/(n.replace('.','/')+'.olean')]
 p=next((p for p in ps if p.is_file()),None);assert p is not None,(n,ps)
 objs[n]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
cfg['deps_fingerprint']['selected_objects']=objs
(B/(cfg['attempt']+'.json')).write_text(json.dumps(cfg,indent=2)+'\\n')
"""%(B,T,json.dumps(row),json.dumps(cfg))
 r=subprocess.run(['ssh',H,'python3 -'],input=payload,text=True,capture_output=True)
 if r.returncode:raise SystemExit('STOP dependency pin: '+r.stderr)
 collect(a+'.json')
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 receipt=json.loads((E/a/'receipt.json').read_text());state[m]='passed' if receipt['exit_status']==0 else 'failed'
 (E/'RPz_state.json').write_text(json.dumps(dict(attempts=attempt,state=state,blocked=blocked),indent=2)+'\n')
 print(a,m,'exit',receipt['exit_status'],'wall',round(receipt['wall_seconds'],2),'rss',receipt['peak_rss_kib'],flush=True)
(E/'RPz_state.json').write_text(json.dumps(dict(attempts=attempt,state=state,blocked=blocked),indent=2)+'\n')
print('Replay phase stopped:',attempt,'attempts; audit attempt reserved',flush=True)
