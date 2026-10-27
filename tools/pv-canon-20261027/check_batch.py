"""Finite, sequential focused build in one admitted 8G scope; never an idle reservation."""
from pathlib import Path
import subprocess,json,hashlib,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-canon-20261027';B='/home/dombarker/project-offloads';D=B+'/codex-pv-canon-20261027';H='dombarker@100.108.41.90';tp=E/'tally.json';t=json.loads(tp.read_text());modules=sys.argv[1:];assert modules and len(modules)<=97-t['lean']
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();plan=[]
for m in modules:
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');assert p.name.startswith('PV_Canon_');n=t['next_id'];assert n<44497;t['next_id']+=1;t['attempts'].append(dict(id=n,module=m,planned_batch=True));plan.append(dict(id=n,module=m,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));(E/f'{n}-source.lean.txt').write_bytes(p.read_bytes())
tp.write_text(json.dumps(t,indent=2)+'\n');tag='batch-'+str(plan[0]['id']);(E/(tag+'-plan.json')).write_text(json.dumps(dict(revision=rev,plan=plan),indent=2)+'\n')
precode="from pathlib import Path; import subprocess; O=Path("+repr(D)+")/'preflight'/"+repr(tag)+"; O.mkdir(parents=True); r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(O/'reservation.json')],stdout=open(O/'reservation.log','w'),stderr=subprocess.STDOUT); print((O/'reservation.log').read_text()); raise SystemExit(r.returncode)"
pre=subprocess.run(['ssh',H,'python3 -'],input=precode,text=True,capture_output=True);(E/(tag+'-reservation.log')).write_text(pre.stdout+pre.stderr)
if pre.returncode:print(pre.stdout+pre.stderr+'UNCHARGED; wait 180s');raise SystemExit(pre.returncode)
for item in plan:
 m=item['module'];p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');subprocess.run(['scp',str(p),H+':'+D+'/sources/'+m+'.lean'],check=True,stdout=subprocess.DEVNULL)
worker='''from pathlib import Path
import json,subprocess,time,hashlib,re
D=Path(DIR);B=Path('/home/dombarker/project-offloads');plan=PLAN;e=json.loads((D/'env.json').read_text())
for item in plan:
 n=item['id'];m=item['module'];O=D/'receipts'/str(n);O.mkdir(parents=True,exist_ok=False);src=D/'sources'/(m+'.lean');obj=D/'objects'/(m+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 deps={}
 for imported in re.findall(r'^import (\\S+)',src.read_text(),re.M):
  for root in e['LEAN_PATH'].split(':'):
   path=Path(root)/(imported.replace('.','/')+'.olean')
   if path.is_file():deps[imported]=dict(path=str(path.resolve()),sha256=hashlib.sha256(path.read_bytes()).hexdigest());break
 meta=dict(target=m,attempt=n,revision=REVISION,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),dependencies=deps,caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),batch=TAG)
 started=time.monotonic();cmd=['timeout','900','python3',str(B/'aspis-fs-generic-20261006/evidence/run2.py'),str(D/'env.json'),str(D/'objects'),str(D/'sources'),str(obj),str(src),'7000']
 r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],stdout=open(O/'out.log','w'),stderr=subprocess.STDOUT)
 meta.update(exit=r.returncode,wall_seconds=time.monotonic()-started,time_log=(O/'time.log').read_text(),axioms=[line for line in (O/'out.log').read_text().splitlines() if 'axioms' in line]);(O/'receipt.json').write_text(json.dumps(meta,indent=2));print(str(n)+' '+m+' exit='+str(r.returncode),flush=True)
 if r.returncode:print((O/'out.log').read_text(),flush=True);break
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
