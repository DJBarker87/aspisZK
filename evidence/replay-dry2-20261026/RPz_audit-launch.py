"""Partition fresh declaration audits into the remaining attempt budget."""
from pathlib import Path
import json,subprocess,time,math
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-replay-dry-20261026';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
def ssh(cmd):return subprocess.run(['ssh',H,cmd],text=True,capture_output=True)
def collect(name):
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['scp','-q',H+':'+B+'/'+name,str(p)],capture_output=True,text=True)
 if r.returncode:raise SystemExit('STOP collection: '+r.stderr)
audit_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
state=json.loads((E/'RPz_state.json').read_text());used=state['attempts'];remaining=600-used
passed=[m for m,s in state['state'].items() if s=='passed'];groups=[]
# Nonoverlapping query groups. If necessary partition a module's declarations by
# name hash; no declaration's axioms are queried twice in the explicit audit.
if remaining<=len(passed):
 for i in range(remaining):groups.append((passed[i*len(passed)//remaining:(i+1)*len(passed)//remaining],0,1))
else:
 base,extra=divmod(remaining,len(passed))
 for i,m in enumerate(passed):
  buckets=base+(i<extra)
  for b in range(buckets):groups.append(([m],b,buckets))
template=(E/'RPz_audit-template.txt').read_text()
for i,(ms,bucket,buckets) in enumerate(groups,1):
 a=f'RPz_{used+i:03d}';name=f'RPz_Audit{i:03d}';rel=name+'.lean'
 src=template.replace('@@IMPORTS@@','\n'.join('import '+m for m in ms)).replace('@@SELECTED@@','#[ '+', '.join('`'+m for m in ms)+' ]').replace('if selected.contains owner then',f'if selected.contains owner && n.hash.toNat % {buckets} == {bucket} then')
 (E/rel).write_text(src)
 if (E/a/'receipt.json').exists():continue
 for retry in range(11):
  reservation=f'{B}/{a}-reservation.json';barrier=f'{B}/{a}-barrier-{retry}.log'
  r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {reservation} > {barrier} 2>&1');collect(a+f'-barrier-{retry}.log')
  exists=ssh(f'test -f {reservation}').returncode==0
  if not exists and retry==0:time.sleep(30);continue
  if r.returncode==0:collect(a+'-reservation.json');break
  if r.returncode==78 and retry<10:print(a,'reservation wait 180s',flush=True);time.sleep(180);continue
  log=(E/(a+f'-barrier-{retry}.log')).read_text()
  if 'FileNotFoundError' in log and retry==0:time.sleep(30);continue
  raise SystemExit('STOP audit admission: '+log)
 else:raise SystemExit('STOP audit admission retries exhausted')
 r=subprocess.run(['scp','-q',str(E/rel),H+':'+B+'/'+rel],capture_output=True,text=True)
 if r.returncode:raise SystemExit(r.stderr)
 cfg=dict(attempt=a,kind='lean',module=name,audit_modules=ms,audit_bucket=bucket,audit_buckets=buckets,sources=[rel],source_revision=audit_revision,source_tree_dirty=True,env={'LEAN_PATH':T+'/lib/lean:'+B+'/RPz_objects:'+B+'/RPz_trusted'},command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o',name+'.olean',rel],timeout=540,deps_fingerprint={'scope':'Fresh-object #print axioms via standard Lean API for a disjoint declaration partition'},expected_time='Precomputed exported axiom queries; no source replay or arithmetic generation',reservation_retries=retry)
 payload="""import json,hashlib
from pathlib import Path
B=Path(%r);T=Path(%r);ms=json.loads(%r);cfg=json.loads(%r);objs={}
for n in ['Lean']+ms:
 ps=[T/'lib/lean'/(n.replace('.','/')+'.olean'),B/'RPz_objects'/(n.replace('.','/')+'.olean')]
 p=next(p for p in ps if p.is_file());objs[n]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
cfg['deps_fingerprint']['selected_objects']=objs
(B/(cfg['attempt']+'.json')).write_text(json.dumps(cfg,indent=2)+'\\n')
"""%(B,T,json.dumps(ms),json.dumps(cfg))
 r=subprocess.run(['ssh',H,'python3 -'],input=payload,text=True,capture_output=True)
 if r.returncode:raise SystemExit(r.stderr)
 collect(a+'.json')
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 d=json.loads((E/a/'receipt.json').read_text())
 print(a,name,'modules',len(ms),'exit',d['exit_status'],'wall',round(d['wall_seconds'],2),'rss',d['peak_rss_kib'],flush=True)
 # Failed partitions are retained, never rerun unchanged. For an ordinary type
 # error, correct only subsequent distinct audit modules; never loop a failure.
 if d['exit_status']!=0:raise SystemExit('STOP audit partition failure; inspect before remaining queries')
