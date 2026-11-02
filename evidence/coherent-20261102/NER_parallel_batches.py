"""Dependency-ready batches, at most two independently admitted 8 GiB scopes."""
import concurrent.futures as cf,hashlib,json,subprocess,time,sys
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parent.parent
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-cx-coherent-cache-20261102';L='/home/dombarker/project-offloads/codex-cx-fixture-cache-20261027';S='/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
plan=json.loads((E/'NER_REBUILD_PLAN.json').read_text())['modules'];required={r['module'] for r in plan}
done={r['module'] for r in json.loads((E/'NER_REBUILT_OBJECT_PINS.json').read_text())}
for p in sorted(E.glob('NER_B*-details/modules.jsonl')):
 for line in p.read_text().splitlines():
  r=json.loads(line)
  if r['exit_status']==0:done.add(r['module'])
  else:sys.exit('Existing failed branch: '+r['module'])
todo={r['module']:r for r in plan if r['module'] not in done}
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
def run(args,**kw):return subprocess.run(args,check=True,**kw)
def event(x):
 with (E/'NER_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(x)+'\n')
def submit(a,batch):
 for retry in range(11):
  p=subprocess.run(['ssh',H,f'python3 {L}/reservation_agg16.py {D}/{a}-reservation-{retry}.json > {D}/{a}-barrier-{retry}.log 2>&1'])
  run(['scp','-q',f'{H}:{D}/{a}-reservation-{retry}.json',f'{H}:{D}/{a}-barrier-{retry}.log',str(E)])
  ad=json.loads((E/f'{a}-reservation-{retry}.json').read_text());event(dict(attempt=a,event='admission',exit=p.returncode,retry=retry,receipt=f'{a}-reservation-{retry}.json'))
  if p.returncode==0 and ad.get('allowed') is True:break
  if p.returncode!=78 or retry==10:raise RuntimeError('Admission failure: '+a)
  time.sleep(180)
 (E/(a+'-modules.json')).write_text(json.dumps(batch,indent=2)+'\n')
 cfg=dict(kind='batch',attempt=a,module=[r['module'] for r in batch],sources=['NER_batch.py',a+'-modules.json'],env={'LEAN_PATH':f'{D}:{D}/objects:{S}:{S}/objects:{T}/lib/lean'},timeout=21600,command=['python3','NER_batch.py',a+'-modules.json',a+'-details'],source_revision=rev,source_tree_dirty=True,deps_fingerprint={'scope':'Dependency-ready disjoint batches; per-module selected direct imports in modules.jsonl'},expected_time='Sequential compilation of listed downstream modules; one Lean process per scope, at most two scopes',reservation_retries=retry)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 run(['scp','-q',str(E/(a+'.json')),str(E/(a+'-modules.json')),H+':'+D+'/'])
 p=subprocess.run(['ssh',H,f'cd {D} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json'],capture_output=True,text=True)
 (E/(a+'-launcher.log')).write_text(p.stdout+p.stderr)
 # No resubmission after transport failure: recover the submitted attempt read-only.
 if p.returncode==255:
  for transport_retry in range(10):
   time.sleep(60)
   probe=subprocess.run(['ssh',H,f'test -f {D}/{a}/receipt.json'])
   event(dict(attempt=a,event='transport_recovery',exit=probe.returncode,retry=transport_retry))
   if probe.returncode==0:break
  else:raise RuntimeError('Unresolved submitted attempt '+a)
 run(['scp','-qr',f'{H}:{D}/{a}',f'{H}:{D}/{a}-details',str(E)])
 receipt=json.loads((E/a/'receipt.json').read_text());status=receipt['exit_status']
 event(dict(attempt=a,event='scope',exit=status,transport_exit=p.returncode,batch=True,receipt=a+'/receipt.json'))
 print(a,status,flush=True)
 return status

def ready_batch():
 chosen=[];local=set(done)
 # Iteration follows the pinned topological order. A second batch cannot use
 # an in-flight object because only successful completed modules enter done.
 for m,r in list(todo.items()):
  if all(dep not in required or dep in local for dep in r['cohort_imports']):
   chosen.append(r);local.add(m)
   if len(chosen)==40:break
 for r in chosen:del todo[r['module']]
 return chosen
next_id=max([int(p.name.split('-')[0][5:]) for p in E.glob('NER_B*-modules.json')]+[0])+1
failed=False
with cf.ThreadPoolExecutor(max_workers=2) as pool:
 active={}
 while todo or active:
  while not failed and len(active)<2 and todo:
   batch=ready_batch()
   if not batch:break
   a=f'NER_B{next_id:03}';next_id+=1
   if next_id>121:raise RuntimeError('120 batch scope budget exhausted')
   active[pool.submit(submit,a,batch)]=(a,batch)
   print('submitted',a,len(batch),'remaining',len(todo),flush=True)
  if not active:raise RuntimeError('No ready batch')
  completed,_=cf.wait(active,timeout=30,return_when=cf.FIRST_COMPLETED)
  for f in completed:
   a,batch=active.pop(f)
   status=f.result()
   if status:failed=True
   else:done.update(r['module'] for r in batch)
  if failed and not active:sys.exit('Compilation failure; branch stopped')
print('All affected modules rebuilt',len(done),flush=True)
