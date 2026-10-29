"""Fail-closed admitted capped scope, shared pinned Lean driver or native analysis."""
from pathlib import Path
import hashlib,json,subprocess,sys,time,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029')
label,kind,*args=sys.argv[1:]
assert not (D/f'{label}-receipt.json').exists()
last=D/'last-refusal.json'
if last.exists():assert time.time()-json.loads(last.read_text())['epoch']>=180
ad=D/f'admission-{label}.json'
with (D/f'admission-{label}.log').open('a') as f:
 a=subprocess.run(['python3',str(D.parent/'codex-pv-runjoin-20261026/reservation-existing.py'),str(ad)],stdout=f,stderr=subprocess.STDOUT)
if a.returncode or not ad.exists() or json.loads(ad.read_text()).get('allowed') is not True:
 last.write_text(json.dumps(dict(epoch=time.time(),label=label,exit=a.returncode)))
 print('REFUSED',label,a.returncode);sys.exit(78)
start=time.time()
if kind=='lean':
 n,module,fp=args;assert 63000<=int(n)<=63099
 cmd=[str(D.parent/'r1-privacy-build-integration-20261019/tools/run-joint.sh'),n,module,'J','7000','8',fp]
else:
 assert kind in ['native','privatelean']
 if kind=='privatelean':
  n,module=args;assert 63000<=int(n)<=63099
  assert not (D/f'lean{n}-receipt.json').exists()
  assert json.loads((D/'resume-cache-preflight.json').read_text())['mismatches']==[]
  src=D/'sources'/(module.replace('.','/')+'.lean');obj=D/'objects'/(module.replace('.','/')+'.olean')
  obj.parent.mkdir(parents=True,exist_ok=True)
  if obj.is_symlink():obj.unlink()
  dependency_objects={}
  for imp in re.findall(r'^import (\S+)',src.read_text(),re.M):
   paths=[D/'objects']+[Path(p) for p in json.loads((D/'env-J.json').read_text())['LEAN_PATH'].split(':')]
   path=next(p/(imp.replace('.','/')+'.olean') for p in paths if (p/(imp.replace('.','/')+'.olean')).is_file())
   dependency_objects[imp]={str(q):hashlib.sha256(q.read_bytes()).hexdigest() for q in [path,Path(str(path)+'.server'),Path(str(path)+'.private'),path.with_suffix('.ir')] if q.is_file()}
  args=['python3',str(D.parent/'aspis-fs-generic-20261006/evidence/run2.py'),str(D/'env-J.json'),str(D/'objects'),str(D/'sources'),str(obj),str(src),'7000']
 cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(D/f'{label}-time.log'),'timeout','900',*args]
with (D/f'{label}-output.log').open('w') as f:p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
rec=dict(target=args,command=cmd,exit=p.returncode,wall_seconds=time.time()-start,admission_exit=a.returncode,admission_allowed=True,source_revision=(D/'revision.txt').read_text().strip(),runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
if kind=='lean':
 T=D.parent/'aspis-fs-generic-20261006/evidence'
 for src,suffix in [(T/f'out-{n}.log','output.log'),(T/f'time-{n}.log','time.log'),(T/f'sha-{n}.txt','sha.txt')]:
  if src.exists():(D/f'{label}-{suffix}').write_bytes(src.read_bytes())
 out=(D/f'{label}-output.log').read_text()
 rec['exit']=int(re.findall(r'^exit=(\d+)',out,re.M)[-1]) if re.findall(r'^exit=(\d+)',out,re.M) else p.returncode
 rec['print_axioms']=out
elif kind=='privatelean':
 rec.update(dependency_objects=dependency_objects,module=module,attempt=int(n),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),dependency_fingerprint=hashlib.sha256((D/'resume-cache-preflight.json').read_bytes()).hexdigest(),environment_sha256=hashlib.sha256((D/'env-J.json').read_bytes()).hexdigest(),print_axioms=(D/f'{label}-output.log').read_text(),object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else None)
else:rec['print_axioms']='N/A: native evidence'
(D/f'{label}-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(label,rec['exit'],(D/f'{label}-output.log').read_text()[-5000:],flush=True)
sys.exit(rec['exit'])
