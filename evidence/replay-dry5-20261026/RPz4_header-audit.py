"""Batched proof-dependency queries using unchanged admission and S2W runner."""
from pathlib import Path
import json,subprocess,time
E=Path(__file__).resolve().parent;R=E.parents[1];H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-replay-dry-20261026';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
SSH=['-o','ControlMaster=auto','-o','ControlPersist=120','-o','ControlPath=/tmp/RPz4-ssh-%h-%p-%r']
def ssh(cmd):return subprocess.run(['ssh',*SSH,H,cmd],capture_output=True,text=True)
def collect(name):
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['scp','-q',*SSH,H+':'+B+'/'+name,str(p)],capture_output=True,text=True)
 if r.returncode:raise SystemExit('STOP collection: '+r.stderr)
roots=json.loads((E/'RPz4_resolution-full.json').read_text())['config']['env']['LEAN_PATH'].split(':')
trusted={'Init','Lean','Std','Lake','Mathlib','Aeneas','AeneasMeta','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Cli'}
statefile=E/'RPz4_coherent-headers.json';graph=json.loads(statefile.read_text()) if statefile.exists() else {'modules':{},'missing':[],'qualification':'Actual object headers selected by ordered Rc7_002 LEAN_PATH; historical object provenance, not fresh replay'}
while True:
 pending=['Rc7_Top'] if not graph['modules'] else list(dict.fromkeys(n for v in graph['modules'].values() for n in v.get('imports',[]) if n.split('.')[0] not in trusted and n not in graph['modules'] and n not in graph['missing']))
 if not pending:break
 ms=pending[:100];used=max(int(f.parent.name.split('_')[1]) for f in E.glob('RPz4_*/receipt.json'));a=f'RPz4_{used+1:03d}';name=f'RPz4_Headers{used+1:03d}'
 assert used<1500
 payload='''import json,hashlib
from pathlib import Path
roots=json.loads(%r);names=json.loads(%r);out={}
for n in names:
 p=next((Path(r)/(n.replace('.','/')+'.olean') for r in roots if (Path(r)/(n.replace('.','/')+'.olean')).is_file()),None)
 out[n]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} if p else None
print(json.dumps(out))
'''%(json.dumps(roots),json.dumps(ms))
 r=subprocess.run(['ssh',*SSH,H,'python3 -'],input=payload,text=True,capture_output=True);assert r.returncode==0,r.stderr;pins=json.loads(r.stdout)
 for n,pin in pins.items():
  if pin is None:graph['missing'].append(n)
 pins={n:v for n,v in pins.items() if v};statefile.write_text(json.dumps(graph,indent=2)+'\n')
 if not pins:continue
 src='import Lean\nopen Lean Elab Command\n'
 for n,pin in pins.items():
  src+='run_cmd do\n  let (data, _) ← liftIO <| readModuleData '+json.dumps(pin['path'])+'\n'
  src+='  logInfo m!"RPZ4_HEADER {(Json.mkObj [(\"module\", toJson '+json.dumps(n)+'), (\"imports\", toJson (data.imports.map (·.module.toString)))]).compress}"\n'
 src+='run_cmd logInfo "RPZ4_HEADERS_COMPLETE"\n';rel=name+'.lean';(E/rel).write_text(src)
 for retry in range(11):
  reservation=f'{B}/{a}-reservation.json';barrier=f'{B}/{a}-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {reservation} > {barrier} 2>&1');collect(a+f'-barrier-{retry}.log');exists=ssh(f'test -f {reservation}').returncode==0
  if not exists and retry==0:time.sleep(30);continue
  if r.returncode==0:collect(a+'-reservation.json');break
  if r.returncode==78 and retry<10:print(a,'reservation wait 180s',flush=True);time.sleep(180);continue
  log=(E/(a+f'-barrier-{retry}.log')).read_text()
  if 'FileNotFoundError' in log and retry==0:time.sleep(30);continue
  raise SystemExit('STOP admission: '+log)
 else:raise SystemExit('STOP admission retries exhausted')
 r=subprocess.run(['scp','-q',*SSH,str(E/rel),H+':'+B+'/'+rel],capture_output=True,text=True);assert r.returncode==0,r.stderr
 cfg=dict(attempt=a,kind='lean',module=name,sources=[rel],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,env={'LEAN_PATH':T+'/lib/lean'},command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o',name+'.olean',rel],timeout=540,deps_fingerprint={'scope':'Read selected historical repository object headers only; no theorem is accepted by this query','selected_objects':pins},expected_time='At most 100 object-header queries; no recurrence evaluation or source compilation',reservation_retries=retry)
 payload='from pathlib import Path\nPath('+repr(B+'/'+a+'.json')+').write_text('+repr(json.dumps(cfg,indent=2)+'\n')+')\n';r=subprocess.run(['ssh',*SSH,H,'python3 -'],input=payload,text=True,capture_output=True);assert r.returncode==0,r.stderr;collect(a+'.json')
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json');(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 receipt=json.loads((E/a/'receipt.json').read_text());print(a,'headers',len(pins),'exit',receipt['exit_status'],'wall',round(receipt['wall_seconds'],2),flush=True)
 if receipt['exit_status']!=0:raise SystemExit('STOP header audit failure; inspect and split before retry')
 log=(E/a/'stdout.log').read_text();assert 'RPZ4_HEADERS_COMPLETE' in log
 for line in log.splitlines():
  if line.startswith('RPZ4_HEADER '):
   v=json.loads(line[12:]);graph['modules'][v['module']]={**pins[v['module']],'imports':v['imports']}
 statefile.write_text(json.dumps(graph,indent=2)+'\n')
print('Selected historical graph:',len(graph['modules']),'repository modules; missing',graph['missing'],flush=True)
