"""One fail-closed admitted scope; private sources/objects only. No shared edits."""
from pathlib import Path
import hashlib,json,subprocess,sys,time,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag7-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
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
rec=dict(kind=kind,admission_exit=a.returncode,admission_allowed=True,source_revision=(D/'revision.txt').read_text().strip(),runner_sha256=sha(Path(__file__)),resource_caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
if kind=='lean':
 n,module=args;assert 65700<=int(n)<=65799
 src=D/'sources'/(module.replace('.','/')+'.lean');obj=D/'objects'/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 assert not obj.is_symlink()
 env=json.loads((D/'env-J.json').read_text());deps={}
 for imp in re.findall(r'^import (\S+)',src.read_text(),re.M):
  paths=[Path(p) for p in env['LEAN_PATH'].split(':')]
  p=next(p/(imp.replace('.','/')+'.olean') for p in paths if (p/(imp.replace('.','/')+'.olean')).is_file())
  deps[imp]={str(q):sha(q) for q in [p,Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')] if q.is_file()}
 rec.update(module=module,attempt=int(n),source_sha256=sha(src),environment_sha256=sha(D/'env-J.json'),dependency_objects=deps,Lean_M=7000)
 (D/f'{label}-source.lean.txt').write_bytes(src.read_bytes())
 args=['python3',str(D.parent/'aspis-fs-generic-20261006/evidence/run2.py'),str(D/'env-J.json'),str(D/'objects'),str(D/'sources'),str(obj),str(src),'7000']
else:
 assert kind=='native'
 inputs={}
 for i,arg in enumerate(args):
  if i and args[i-1]=='-o':continue
  path=Path(arg)
  if path.is_file() and path.is_relative_to(D):
   inputs[str(path)]=dict(sha256=sha(path),bytes=path.stat().st_size)
   if path.suffix in {'.rs','.py','.lean'}:
    snapshot=D/(label+'-input-'+path.name+'.txt');snapshot.write_bytes(path.read_bytes());inputs[str(path)]['snapshot']=str(snapshot)
 rec['input_artifacts']=inputs
cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(D/f'{label}-time.log'),'timeout','900',*args]
start=time.time()
with (D/f'{label}-output.log').open('w') as f:p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
out=(D/f'{label}-output.log').read_text();tim=(D/f'{label}-time.log').read_text()
def metric(pattern):
 m=re.search(pattern,tim);return m[1] if m else None
rec.update(command=cmd,exit=p.returncode,wall_seconds=time.time()-start,peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)'),swaps=metric(r'Swaps: (\d+)'),gnu_wall=metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)'),print_axioms=out if kind=='lean' else 'N/A: native source/control evidence')
if kind=='lean':rec['object_sha256']=sha(obj) if obj.exists() else None
(D/f'{label}-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(label,rec['exit'],out[-6000:],flush=True);sys.exit(rec['exit'])
