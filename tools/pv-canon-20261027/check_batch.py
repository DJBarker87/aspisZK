"""Finite, sequential focused build in one admitted 8G scope; continue only independent targets after errors; never an idle reservation."""
from pathlib import Path
import subprocess,json,hashlib,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-canon-20261027';B='/home/dombarker/project-offloads';D=B+'/codex-pv-canon-20261027';H='dombarker@100.108.41.90';tp=E/'tally.json';t=json.loads(tp.read_text());modules=[a for a in sys.argv[1:] if a!='--audit'];audit='--audit' in sys.argv;assert modules and len(modules)<=(100 if audit else 97)-t['lean']
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();plan=[]
# Only the first ID is consumed by a refusal; the rest are assigned after admission.
m=modules[0];p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');assert p.name.startswith('PV_Canon_')
n=t['next_id'];assert n<=(44499 if audit else 44496);t['next_id']+=1;t['attempts'].append(dict(id=n,module=m,planned_batch=True))
plan=[dict(id=n,module=m,sha256=hashlib.sha256(p.read_bytes()).hexdigest())]
tp.write_text(json.dumps(t,indent=2)+'\n');tag='batch-'+str(n)
(E/(tag+'-plan.json')).write_text(json.dumps(dict(revision=rev,plan=plan,pending_unassigned=modules[1:]),indent=2)+'\n')
precode="from pathlib import Path; import subprocess; O=Path("+repr(D)+")/'preflight'/"+repr(tag)+"; O.mkdir(parents=True); r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(O/'reservation.json')],stdout=open(O/'reservation.log','w'),stderr=subprocess.STDOUT); print((O/'reservation.log').read_text()); raise SystemExit(r.returncode)"
pre=subprocess.run(['ssh',H,'python3 -'],input=precode,text=True,capture_output=True);(E/(tag+'-reservation.log')).write_text(pre.stdout+pre.stderr)
if pre.returncode:print(pre.stdout+pre.stderr+'UNCHARGED; wait 180s');raise SystemExit(pre.returncode)
for m in modules[1:]:
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');assert p.name.startswith('PV_Canon_')
 n=t['next_id'];assert n<=(44499 if audit else 44496);t['next_id']+=1;t['attempts'].append(dict(id=n,module=m,planned_batch=True));plan.append(dict(id=n,module=m,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
tp.write_text(json.dumps(t,indent=2)+'\n');(E/(tag+'-plan.json')).write_text(json.dumps(dict(revision=rev,plan=plan),indent=2)+'\n')
for item in plan:
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(item['module']+'.lean');(E/f"{item['id']}-source.lean.txt").write_bytes(p.read_bytes())
assert all(Path(item['module']).parent==Path('R1Z') for item in plan)
subprocess.run(['scp',*[str(R/'docs/research/v8-r0-zk-20261009/lean'/(item['module']+'.lean')) for item in plan],H+':'+D+'/sources/R1Z/'],check=True,stdout=subprocess.DEVNULL)
worker='''from pathlib import Path
import json,subprocess,time,hashlib,re
D=Path(DIR);B=Path('/home/dombarker/project-offloads');plan=PLAN;e=json.loads((D/'env.json').read_text())
failed=set()
for item in plan:
 n=item['id'];m=item['module'];src=D/'sources'/(m+'.lean')
 own_imports=[a.replace('.','/') for a in re.findall(r'^import (\\S+)',src.read_text(),re.M) if a.split('.')[-1].startswith('PV_Canon_')]
 if any(a in failed or not (D/'objects'/(a+'.olean')).exists() for a in own_imports):
  print(str(n)+' '+m+' SKIP failed/missing predecessor',flush=True);failed.add(m);continue
 O=D/'receipts'/str(n);O.mkdir(parents=True,exist_ok=False);src=D/'sources'/(m+'.lean');obj=D/'objects'/(m+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 deps={}
 for imported in re.findall(r'^import (\\S+)',src.read_text(),re.M):
  for root in e['LEAN_PATH'].split(':'):
   path=Path(root)/(imported.replace('.','/')+'.olean')
   if path.is_file():deps[imported]=dict(path=str(path.resolve()),sha256=hashlib.sha256(path.read_bytes()).hexdigest());break
 meta=dict(target=m,attempt=n,revision=REVISION,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),dependencies=deps,caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),batch=TAG)

 for previous in (D/'receipts').glob('*/receipt.json'):
  old=json.loads(previous.read_text())
  if old.get('source_sha256')==meta['source_sha256'] and old.get('dependencies')==meta.get('dependencies'):
   raise SystemExit('REFUSED unchanged source and imported objects: '+str(previous))
 started=time.monotonic();cmd=['timeout','900','python3',str(B/'aspis-fs-generic-20261006/evidence/run2.py'),str(D/'env.json'),str(D/'objects'),str(D/'sources'),str(obj),str(src),'7000']
 r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],stdout=open(O/'out.log','w'),stderr=subprocess.STDOUT)
 meta.update(exit=r.returncode,wall_seconds=time.monotonic()-started,time_log=(O/'time.log').read_text(),axioms=[line for line in (O/'out.log').read_text().splitlines() if 'axioms' in line]);(O/'receipt.json').write_text(json.dumps(meta,indent=2));print(str(n)+' '+m+' exit='+str(r.returncode),flush=True)
 if r.returncode:print((O/'out.log').read_text(),flush=True);failed.add(m)
'''.replace('DIR',repr(D)).replace('PLAN',repr(plan)).replace('REVISION',repr(rev)).replace('TAG',repr(tag))
# Worker is a finite proof-target queue, running under the existing admission barrier.
subprocess.run(['ssh',H,'cat > '+D+'/'+tag+'.py'],input=worker,text=True,check=True)
code='''from pathlib import Path
import subprocess
D=Path(DIR);G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy');O=D/'preflight'/TAG
r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'barrier.json'),'python3',str(D/(TAG+'.py'))]);raise SystemExit(r.returncode)
'''.replace('DIR',repr(D)).replace('TAG',repr(tag))
r=subprocess.run(['ssh',H,'python3 -'],input=code,text=True,capture_output=True);print(r.stdout+r.stderr);(E/(tag+'-scope.log')).write_text(r.stdout+r.stderr)
for item in plan:
 n=item['id'];result=subprocess.run(['scp','-r',H+':'+D+'/receipts/'+str(n),str(E)],capture_output=True,text=True);rp=E/str(n)/'receipt.json'
 if rp.exists():
  t=json.loads(tp.read_text());t['lean']+=1
  for a in t['attempts']:
   if a['id']==n:a['charged']=True
  tp.write_text(json.dumps(t,indent=2)+'\n')
