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
 n,module,fp=args;assert 62700<=int(n)<=62799
 cmd=[str(D.parent/'r1-privacy-build-integration-20261019/tools/run-joint.sh'),n,module,'J','7000','8',fp]
else:
 assert kind=='native'
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
else:rec['print_axioms']='N/A: native evidence'
(D/f'{label}-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(label,rec['exit'],(D/f'{label}-output.log').read_text()[-5000:],flush=True)
sys.exit(rec['exit'])
