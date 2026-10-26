"""Serial job orchestration of unchanged reservation and S2W command runner."""
from pathlib import Path
import json,subprocess,time,sys,math
E=Path(__file__).resolve().parent; H='dombarker@100.108.41.90'
SSH=['-o','ControlMaster=auto','-o','ControlPersist=120','-o','ControlPath=/tmp/RPz4-ssh-%h-%p-%r']
B='/home/dombarker/project-offloads/codex-cx-replay-dry-20261026'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
def ssh(cmd):return subprocess.run(['ssh',*SSH,H,cmd],text=True,capture_output=True)
def collect(name):
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['scp','-q',*SSH,H+':'+B+'/'+name,str(p)],capture_output=True,text=True)
 if r.returncode:raise SystemExit('STOP collection: '+r.stderr)
plan=json.loads((E/'RPz4_source-plan.json').read_text());rows=[]
for m in plan['order']:
 x=plan['modules'][m];rows.append(dict(module=m,imports=x['imports'],repository_source=x['source'],source='RPz4_sources/'+m.replace('.','/')+'.lean',object='RPz4_objects/'+m.replace('.','/')+'.olean'))
focus=set(json.loads((E.parents[1]/'evidence/replay-dry4-20261026/RPz3_source-plan.json').read_text())['unresolved']) | {'R1NaturalProjection','ImportUnionNamedDiscriminant','AspisR1SemanticCallExtraction.Types','R1LiteralTranscript','ClaimsUnrolledParentTypes','AspisR1CircleSampleWrapper.Types','AspisR1CircleSampleWrapper.FunsExternal','AspisR1CircleFallback.Types','AspisR1CircleFallback.FunsExternal','AspisR1CircleFallback.Funs'}
focus_closure=set()
def focus_visit(m):
 if m in focus_closure:return
 focus_closure.add(m)
 for n in plan['modules'].get(m,{}).get('imports',[]):focus_visit(n)
for m in focus:focus_visit(m)
rows.sort(key=lambda r:(r['module'] not in focus_closure,r['module'] not in focus,-plan['distance_to_top'].get(r['module'],0)))
state=json.loads((E/'RPz4_reuse.json').read_text())['state'];state={m:v for m,v in state.items() if v in ['passed','failed']};attempt=0;blocked=[]
if (E/'RPz4_state.json').exists():
 prior=json.loads((E/'RPz4_state.json').read_text());state.update({m:v for m,v in prior['state'].items() if v in ['passed','failed']});attempt=max(prior['attempts'],max([int(f.parent.name.split('_')[1]) for f in E.glob('RPz4_*/receipt.json')],default=0))
# Dynamic ready scheduling in critical-distance order. A blocked predecessor never launches.
ordered=[];pending=rows[:];sim=state.copy()
while pending:
 ready=[r for r in pending if r['module'] not in sim and all(plan['modules'].get(n,{}).get('kind')=='trusted-library' or sim.get(n)=='passed' for n in r['imports'])]
 if not ready:break
 r=ready[0];ordered.append(r);sim[r['module']]='passed';pending.remove(r)
rows=ordered
for row in rows:
 m=row['module'];missing=[n for n in row['imports'] if plan['modules'].get(n,{}).get('kind')!='trusted-library' and state.get(n)!='passed']
 if missing:
  state[m]='blocked';blocked.append({'module':m,'missing':missing});continue
 if attempt + math.ceil((sum(v=='passed' for v in state.values())+1)/100) >= 1500:break
 attempt+=1;a=f'RPz4_{attempt:03d}'
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
 # Admission receipt precedes any source transfer. Keep the existing runner unchanged.
 r=ssh('mkdir -p '+B+'/RPz4_sources/'+m.replace('.','/').rsplit('/',1)[0] if '.' in m else 'mkdir -p '+B+'/RPz4_sources')
 if r.returncode:raise SystemExit('STOP source directory: '+r.stderr)
 r=subprocess.run(['scp','-q',*SSH,str(E.parents[1]/row['repository_source']),H+':'+B+'/'+row['source']],capture_output=True,text=True)
 if r.returncode:raise SystemExit('STOP source transfer: '+r.stderr)
 r=ssh('mkdir -p '+B+'/'+str(__import__('pathlib').Path(row['object']).parent))
 if r.returncode:raise SystemExit('STOP object directory: '+r.stderr)
 cfg=dict(kind='lean',module=m,env={'LEAN_PATH':T+'/lib/lean:'+B+'/RPz4_overlay:'+B+'/RPz4_trusted:'+B+'/RPz_trusted'},timeout=540,command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R',row['source'].split('/')[0],'-o',row['object'],row['source']],sources=[row['source']],attempt=a,source_revision=plan['revision'],source_tree_dirty=False,deps_fingerprint={'scope':'fresh repository closure; release-pinned toolchain/library objects only','toolchain':'leanprover/lean4:v4.32.0'},expected_time='one committed repository module elaboration and kernel checking; no generated arithmetic probe',repository_source=row['repository_source'],reservation_retries=retry)
 # Pin actual direct predecessors before calling the existing runner.
 payload="""import json,hashlib
from pathlib import Path
B=Path(%r);T=Path(%r);row=json.loads(%r);cfg=json.loads(%r);objs={}
for n in row['imports']:
 ps=[T/'lib/lean'/(n.replace('.','/')+'.olean'),B/'RPz4_overlay'/(n.replace('.','/')+'.olean'),B/'RPz4_trusted'/(n.replace('.','/')+'.olean'),B/'RPz_trusted'/(n.replace('.','/')+'.olean')]
 p=next((p for p in ps if p.is_file()),None);assert p is not None,(n,ps)
 objs[n]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
cfg['deps_fingerprint']['selected_objects']=objs
(B/(cfg['attempt']+'.json')).write_text(json.dumps(cfg,indent=2)+'\\n')
"""%(B,T,json.dumps(row),json.dumps(cfg))
 r=subprocess.run(['ssh',*SSH,H,'python3 -'],input=payload,text=True,capture_output=True)
 if r.returncode:raise SystemExit('STOP dependency pin: '+r.stderr)
 collect(a+'.json')
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 receipt=json.loads((E/a/'receipt.json').read_text());state[m]='passed' if receipt['exit_status']==0 else 'failed'
 if receipt['exit_status']==0:
  # A complete job-owned namespace view avoids Lean prefix-directory shadowing.
  # Output stays a regular RPz4_objects file; never write through a baseline link.
  payload="""from pathlib import Path
import json,hashlib
B=Path(%r);rel=%r;out={}
p=B/rel
assert p.is_file() and not p.is_symlink(),p
for ext in ['', '.server','.private','IR']:
 src=p.with_suffix('.ir') if ext=='IR' else Path(str(p)+ext)
 if not src.is_file():continue
 key=(rel.removeprefix('RPz4_objects/')[:-6]+'.ir') if ext=='IR' else rel.removeprefix('RPz4_objects/')+ext
 dst=B/'RPz4_overlay'/key;dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists() or dst.is_symlink():
  assert dst.is_symlink(),dst
  if dst.resolve()!=src.resolve():dst.unlink();dst.symlink_to(src)
 else:dst.symlink_to(src)
 out[str(dst)]={'target':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'bytes':src.stat().st_size}
print(json.dumps(out))
"""%(B,row['object'])
  r=subprocess.run(['ssh',*SSH,H,'python3 -'],input=payload,text=True,capture_output=True)
  if r.returncode:raise SystemExit('STOP job namespace view: '+r.stderr)
  with (E/'RPz4_overlay-additions.jsonl').open('a') as out:out.write(json.dumps({'attempt':a,'module':m,'artifacts':json.loads(r.stdout)})+'\n')
 (E/'RPz4_state.json').write_text(json.dumps(dict(attempts=attempt,state=state,blocked=blocked),indent=2)+'\n')
 print(a,m,'exit',receipt['exit_status'],'wall',round(receipt['wall_seconds'],2),'rss',receipt['peak_rss_kib'],flush=True)
(E/'RPz4_state.json').write_text(json.dumps(dict(attempts=attempt,state=state,blocked=blocked),indent=2)+'\n')
print('Replay phase stopped:',attempt,'attempts',flush=True)
