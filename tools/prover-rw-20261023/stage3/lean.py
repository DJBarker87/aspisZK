"""Run one assigned env-J attempt; retain exact inputs and all diagnostics."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
E=H/'stage3'; E.mkdir(exist_ok=True)
a=int(sys.argv[1]); module=sys.argv[2]; assert 11200<=a<=11399
assert module.startswith(('ProverRwSampler/','R1Z/ProverRw'))
source=J/'sources'/(module+'.lean'); s=source.read_text(); deps=[]
for line in s.splitlines():
 if line.startswith('import '):
  for m in line[7:].split():
   p=J/'objects'/(m.replace('.','/')+'.olean')
   deps.append(dict(module=m,object_sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None))
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
(E/f'{a}.lean.txt').write_text(s)
(E/f'{a}-input.json').write_text(json.dumps(dict(module=module,source_revision=(E/'revision.txt').read_text().strip(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),dependencies=deps,deps_fingerprint=fp,source_path=str(source)),indent=2)+'\n')
p=subprocess.run(['sh',str(H/'src/tools/prover-rw-20261023/stage3/run-joint.sh'),str(a),module,'J','7000','7',fp],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(p.stdout+p.stderr);print(p.stdout+p.stderr)
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
for kind,ext in [('out','log'),('time','log'),('sha','txt')]:
 q=T/f'{kind}-{a}.{ext}'
 if q.exists():(E/q.name).write_bytes(q.read_bytes())
log=(E/f'out-{a}.log').read_text() if (E/f'out-{a}.log').exists() else ''
t=(E/f'time-{a}.log').read_text() if (E/f'time-{a}.log').exists() else ''
rec=json.loads((E/f'{a}-input.json').read_text());rec.update(attempt=a,launcher_exit=p.returncode,exit_status=int(re.search(r'^exit=(\d+)',log,re.M)[1]) if re.search(r'^exit=(\d+)',log,re.M) else None,time_log=t,print_axioms=[l for l in log.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],errors=[l for l in log.splitlines() if 'error:' in l],limits=dict(lean_memory_mb=7000,memory_high='5G',memory_max='7G',swap_max=0,tasks_max=64))
(E/f'{a}-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
sys.exit(0 if rec['exit_status']==0 else 1)
