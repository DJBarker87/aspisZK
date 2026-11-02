"""Submit authorized batches through shared admission and unchanged capped runner."""
import hashlib,json,subprocess,tarfile,time,sys
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parent.parent
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-cx-coherent-cache-20261102';L='/home/dombarker/project-offloads/codex-cx-fixture-cache-20261027';S='/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
plan=json.loads((E/'NER_REBUILD_PLAN.json').read_text())['modules'];done={r['module'] for r in json.loads((E/'NER_REBUILT_OBJECT_PINS.json').read_text())}
rows=[r for r in plan if r['module'] not in done]
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
def run(args,**kw):return subprocess.run(args,check=True,**kw)
def event(x):
 with (E/'NER_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(x)+'\n')
# Transfer exactly pinned sources once, with no source changes.
with tarfile.open('/tmp/NER_sources.tar','w') as tar:
 for r in rows:
  p=R/r['repository_source'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
  tar.add(p,arcname=r['module'].replace('.','/')+'.lean')
run(['scp','-q','/tmp/NER_sources.tar',str(E/'NER_batch.py'),H+':'+D+'/'])
run(['ssh',H,f'cd {D} && tar xf NER_sources.tar'])
for i in range(0,len(rows),40):
 a=f'NER_B{i//40+1:03}';batch=rows[i:i+40]
 if (E/a/'receipt.json').exists():
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0;continue
 for retry in range(11):
  p=subprocess.run(['ssh',H,f'python3 {L}/reservation_agg16.py {D}/{a}-reservation-{retry}.json > {D}/{a}-barrier-{retry}.log 2>&1'])
  run(['scp','-q',f'{H}:{D}/{a}-reservation-{retry}.json',f'{H}:{D}/{a}-barrier-{retry}.log',str(E)])
  ad=json.loads((E/f'{a}-reservation-{retry}.json').read_text());event(dict(attempt=a,event='admission',exit=p.returncode,retry=retry,receipt=f'{a}-reservation-{retry}.json'))
  if p.returncode==0 and ad.get('allowed') is True:break
  if p.returncode!=78 or retry==10:sys.exit('Admission failure')
  time.sleep(180)
 (E/(a+'-modules.json')).write_text(json.dumps(batch,indent=2)+'\n')
 cfg=dict(kind='batch',attempt=a,module=[r['module'] for r in batch],sources=['NER_batch.py',a+'-modules.json'],env={'LEAN_PATH':f'{D}:{D}/objects:{S}:{S}/objects:{T}/lib/lean'},timeout=21600,command=['python3','NER_batch.py',a+'-modules.json',a+'-details'],source_revision=rev,source_tree_dirty=True,deps_fingerprint={'scope':'Pinned import-ordered rebuild overlay; each selected direct import recorded in modules.jsonl'},expected_time='Sequential compilation of listed downstream modules, at most one Lean process',reservation_retries=retry)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 run(['scp','-q',str(E/(a+'.json')),str(E/(a+'-modules.json')),H+':'+D+'/'])
 p=subprocess.run(['ssh',H,f'cd {D} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json'],capture_output=True,text=True)
 (E/(a+'-launcher.log')).write_text(p.stdout+p.stderr)
 run(['scp','-qr',f'{H}:{D}/{a}',f'{H}:{D}/{a}-details',str(E)])
 event(dict(attempt=a,event='scope',exit=p.returncode,batch=True,receipt=a+'/receipt.json'))
 print(a,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
