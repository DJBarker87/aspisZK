"""Read-only collection of immutable attempt evidence; never launches jobs."""
from pathlib import Path
import subprocess,sys,json,re,hashlib
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw-step-20261026';e.mkdir(exist_ok=True)
h='dombarker@100.108.41.90:';b='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023';t='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
def fetch(src,dest,required=True):
 x=subprocess.run(['scp',h+src,str(dest)],capture_output=True,text=True)
 if required and x.returncode:raise RuntimeError(x.stderr)
 return x.returncode==0
for arg in sys.argv[1:]:
 if arg.isdigit():
  a=int(arg);assert 23700<=a<=23999
  for src in [f'{b}/pv-rw-step/{a}-input.json',f'{b}/pv-rw-step/{a}.lean.txt',f'{b}/pv-rw-step/{a}-admission.json',f'{b}/pv-rw-step/{a}-admission.log',f'{t}/out-{a}.log',f'{t}/time-{a}.log',f'/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/evidence/{a}-admission-before.json',f'/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/evidence/{a}-admission-barrier.json']:
   fetch(src,e,required='-input.json' in src or '.lean.txt' in src or '/out-' in src)
  x=json.loads((e/f'{a}-input.json').read_text());fetch(f"{b}/pv-rw-step/"+x['dependencies_manifest'],e)
  s=(e/f'out-{a}.log').read_text();tp=e/f'time-{a}.log';ts=tp.read_text() if tp.exists() else ''
  m=re.search(r'^exit=(\d+)',s,re.M);x.update(exit_status=int(m[1]) if m and ts else None,time_log=ts,print_axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",s),errors=[l for l in s.splitlines() if 'error:' in l],command=f"sh {x['launcher']} {a} {x['module']} J 7000 8 {x['deps_fingerprint']}")
  assert hashlib.sha256((e/f'{a}.lean.txt').read_bytes()).hexdigest()==x['source_sha256']
  (e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n')
 else:
  assert arg.startswith('pv-rw-step-') and '/' not in arg
  d=e/arg;d.mkdir(exist_ok=True)
  for n in ['receipt.json','preflight.json','stdout.log','stderr.log','time.log','reservation-at-barrier.json']:
   fetch(f'{b}/src/receipts/{arg}/{n}',d)
