"""Evidence-only serial orchestration; uses the unchanged S2W runner/barrier."""
from pathlib import Path
import json,subprocess,hashlib,time,sys,shlex
E=Path(__file__).resolve().parent;ROOT=E.parents[1];H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
OVERLAY=B+'/DFm_objects';TOOLCHAIN=T+'/lib/lean'
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
def ssh(cmd,**kwargs):return subprocess.run(['ssh',H,cmd],text=True,capture_output=True,**kwargs)
def collect(remote,local):
 local.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['scp','-q',H+':'+B+'/'+remote,str(local)],text=True,capture_output=True)
 if r.returncode:raise SystemExit(r.stderr)
def run(i,module,src,mode='after'):
 a=f'DFm_{i:03d}';rel='DFm_sources/'+module.replace('.','/')+'.lean';out='DFm_objects/'+module.replace('.','/')+'.olean'
 if (E/a/'receipt.json').exists():raise SystemExit('Refusing reused attempt '+a)
 local=E/'DFm_sources'/Path(module.replace('.','/')+'.lean');local.parent.mkdir(parents=True,exist_ok=True);local.write_text(src)
 # No source/config scp before the reservation receipt exists.
 transient=0
 for retry in range(11):
  res=B+'/'+a+'-reservation.json';log=B+'/'+a+f'-barrier-{retry}.log'
  r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {res} > {log} 2>&1')
  collect(a+f'-barrier-{retry}.log',E/(a+f'-barrier-{retry}.log'))
  exists=ssh('test -f '+res).returncode==0
  if not exists or ('FileNotFoundError' in (E/(a+f'-barrier-{retry}.log')).read_text()):
   if transient==0:transient+=1;print(a,'transient reservation; wait 30s',flush=True);time.sleep(30);continue
   raise SystemExit('STOP reservation scanner failed twice')
  collect(a+'-reservation.json',E/(a+'-reservation.json'))
  if r.returncode==0:break
  if r.returncode==78 and retry<10:
   print(a,'reservation contention; wait 180s',flush=True);time.sleep(180);continue
  raise SystemExit('STOP admission '+r.stderr+(E/(a+f'-barrier-{retry}.log')).read_text())
 else:raise SystemExit('STOP reservation budget exhausted')
 paths=[TOOLCHAIN]+([OVERLAY] if mode=='after' else [])+[B,B+'/objects']
 imports=['Init']+[l[7:].strip() for l in src.splitlines() if l.startswith('import ')]
 cfg=dict(attempt=a,kind='lean',module=module,sources=[rel],source_revision=revision,source_tree_dirty=True,env={'LEAN_PATH':':'.join(paths)},command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','DFm_sources','-o',out,rel],timeout=540,deps_fingerprint={'scope':'Evidence-only Debug deletion; isolated overlay on pinned coherent SInt2 objects'},expected_time='one module elaboration or declaration-expression/axioms audit; no arithmetic generation',reservation_retries=retry,mode=mode)
 # Pin each selected direct predecessor before the unchanged runner starts.
 payload='''from pathlib import Path
import hashlib,json
B=Path(%r);cfg=json.loads(%r);paths=json.loads(%r);imports=json.loads(%r);objs={}
for m in imports:
 key=m.replace('.','/')+'.olean';p=next((Path(root)/key for root in paths if (Path(root)/key).is_file()),None)
 if p is None:raise FileNotFoundError(m)
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.exists():objs[str(q)]={'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size}
cfg['deps_fingerprint']['selected_objects']=objs
cfg['deps_fingerprint']['lean_binary_sha256']=hashlib.sha256(Path(%r).read_bytes()).hexdigest()
for key in [%r,%r]: (B/key).parent.mkdir(parents=True,exist_ok=True)
(B/(cfg['attempt']+'.json')).write_text(json.dumps(cfg,indent=2)+'\\n')
'''%(B,json.dumps(cfg),json.dumps(paths),json.dumps(imports),T+'/bin/lean',rel,out)
  # Python sent through stdin; no shell interpolation of source contents.
 r=ssh('python3 -',input=payload)
 if r.returncode:raise SystemExit('STOP pin failure '+r.stderr)
 collect(a+'.json',E/(a+'.json'))
 r=subprocess.run(['scp','-q',str(local),H+':'+B+'/'+rel],text=True,capture_output=True)
 if r.returncode:raise SystemExit(r.stderr)
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f,E/a/f)
 receipt=json.loads((E/a/'receipt.json').read_text())
 print(a,module,'exit',receipt['exit_status'],'wall',round(receipt['wall_seconds'],3),'rss',receipt['peak_rss_kib'],flush=True)
 if receipt['exit_status']!=0:raise SystemExit('STOP failed attempt: inspect, do not rerun unchanged')
def audit(i,modules,label,mode):
 name=f'DFm_Audit{i:03d}';output=f'DFm_{label}.json'
 src=(E/'DFm_audit-template.txt').read_text().replace('@@IMPORTS@@','\n'.join('import '+m for m in modules)).replace('@@SELECTED@@','#[ '+', '.join('`'+m for m in modules)+' ]').replace('@@OUTPUT@@',output)
 run(i,name,src,mode)
 # Large expression snapshots stay on host; hashes/comparison receipts are committed.
inv=json.loads((E/'DFm_inventory.json').read_text());mods=[x['module'] for x in inv['modules']]
phase=sys.argv[1]
if phase=='parsers':
 audit(5,mods,'parser-before','before');audit(6,mods,'parser-after','after')
elif phase=='importers':
 rows=json.loads((E/'DFm_importers.json').read_text());names=[x['module'] for x in rows]
 audit(7,names,'importers-before','before')
 for i,x in enumerate(rows,8):run(i,x['module'],(ROOT/x['source']).read_text())
 for i,x in enumerate(rows[:15],25):audit(i,[x['module']],f'importer-{i}-after','after')
 audit(40,names,'importers-after','after')
else:raise SystemExit('unknown phase')
