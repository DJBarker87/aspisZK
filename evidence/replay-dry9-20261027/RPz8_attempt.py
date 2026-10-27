"""Job receipts around the unchanged admitted S2W runner; one invocation at a time."""
from pathlib import Path
import json,subprocess,time,sys,shlex
E=Path(__file__).resolve().parent;R=E.parents[1]
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-replay-dry-20261026';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
SSH=['-o','ControlMaster=auto','-o','ControlPersist=120','-o','ControlPath=/tmp/RPz8-ssh-%h-%p-%r']
def ssh(cmd,input=None):return subprocess.run(['ssh',*SSH,H,cmd],input=input,text=True,capture_output=True)
def collect(name):
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['scp','-q',*SSH,H+':'+B+'/'+name,str(p)],capture_output=True,text=True)
 if r.returncode:raise RuntimeError('STOP collection: '+r.stderr)
def run(a,m,src,imports,roots=None):
 assert not (E/a/'receipt.json').exists(),a
 for retry in range(11):
  r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier-{retry}.log 2>&1')
  collect(a+f'-barrier-{retry}.log')
  exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
  if not exists and retry==0:time.sleep(30);continue
  if r.returncode==0:collect(a+'-reservation.json');break
  if r.returncode==78 and retry<10:
   print(a,'reservation contention; wait 180s',flush=True);time.sleep(180);continue
  log=(E/(a+f'-barrier-{retry}.log')).read_text()
  if 'FileNotFoundError' in log and retry==0:time.sleep(30);continue
  raise RuntimeError('STOP admission: '+log)
 else:raise RuntimeError('STOP admission retries exhausted')
 r=ssh(f'mkdir -p {B}/RPz8_sources {B}/RPz8_objects')
 if r.returncode:raise RuntimeError(r.stderr)
 rel='RPz8_sources/'+m+'.lean';obj='RPz8_objects/'+m+'.olean'
 r=subprocess.run(['scp','-q',*SSH,str(src),H+':'+B+'/'+rel],capture_output=True,text=True)
 if r.returncode:raise RuntimeError(r.stderr)
 cfg=dict(kind='lean',module=m,env={'LEAN_PATH':':'.join(roots) if roots else T+'/lib/lean:'+B+'/RPz8_overlay:'+B+'/RPz4_trusted:'+B+'/RPz_trusted'},timeout=540,command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','RPz8_sources','-o',obj,rel],sources=[rel],attempt=a,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,deps_fingerprint={'scope':'RPz7 coherent cohort; RPz8 import-only continuation; historical e5c producer; D188 provenance open','toolchain':'leanprover/lean4:v4.32.0'},expected_time='one source module elaboration and kernel checking; no heavy arithmetic expansion planned',repository_source=str(src.relative_to(R)),reservation_retries=retry)
 payload="""import json,hashlib
from pathlib import Path
B=Path(%r);T=Path(%r);cfg=json.loads(%r);objs={}
for n in json.loads(%r):
 ps=[Path(root)/(n.replace('.','/')+'.olean') for root in cfg['env']['LEAN_PATH'].split(':')]
 p=next((p for p in ps if p.is_file()),None);assert p is not None,(n,ps)
 objs[n]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
cfg['deps_fingerprint']['selected_objects']=objs
(B/(cfg['attempt']+'.json')).write_text(json.dumps(cfg,indent=2)+'\\n')
"""%(B,T,json.dumps(cfg),json.dumps(imports))
 r=ssh('python3 -',payload)
 if r.returncode:raise RuntimeError('STOP dependency pin: '+r.stderr)
 collect(a+'.json')
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 receipt=json.loads((E/a/'receipt.json').read_text())
 if receipt['exit_status']==0:
  payload="""from pathlib import Path
import json,hashlib
B=Path(%r);m=%r;out={}
p=B/'RPz8_objects'/(m+'.olean');assert p.is_file() and not p.is_symlink()
for ext in ['', '.server','.private','IR']:
 src=p.with_suffix('.ir') if ext=='IR' else Path(str(p)+ext)
 if not src.is_file():continue
 dst=B/'RPz8_overlay'/src.name
 assert not dst.exists() and not dst.is_symlink(),dst
 dst.symlink_to(src)
 out[str(dst)]={'target':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'bytes':src.stat().st_size}
print(json.dumps(out))
"""%(B,m)
  r=ssh('python3 -',payload)
  if r.returncode:raise RuntimeError('STOP view install: '+r.stderr)
  with (E/'RPz8_overlay-additions.jsonl').open('a') as f:f.write(json.dumps({'attempt':a,'module':m,'artifacts':json.loads(r.stdout)})+'\n')
 print(a,m,'exit',receipt['exit_status'],'wall',round(receipt['wall_seconds'],2),'rss',receipt['peak_rss_kib'],flush=True)
 return receipt
if __name__=='__main__':
 a,m=sys.argv[1:3];run(a,m,E/(m+'.lean'),['Init','CurrentCompactFirstCompositionV1'] if m=='RPz8_PhaseIso' else ['Init','RPz8_PhaseIso'])
