"""Submit only additive modules and retain all attempt evidence locally."""
import pathlib,subprocess,hashlib,json,sys,re
repo=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip()); root=repo/'docs/research/v8-r0-zk-20261009'; ev=pathlib.Path(__file__).resolve().parent
host='dombarker@100.108.41.90'; remote='/home/dombarker/project-offloads/codex-cx-sim-cost5-20261022'
module=sys.argv[1]; attempt=int(sys.argv[2]); assert 8800<=attempt<=8999
src=root/'lean'/f'{module}.lean'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
imports=re.findall(r'^import (\S+)',src.read_text(),re.M)
r={'attempt':attempt,'module':module,'source_sha256':sha(src),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'imports':{m.replace('.','/'):sha(root/'lean'/f"{m.replace('.','/')}.lean") for m in imports}}
(ev/f'source-{attempt}.lean.txt').write_bytes(src.read_bytes())
sub=ev/f'submission-{attempt}.json';sub.write_text(json.dumps(r,indent=2)+'\n')
def run(args,**kw):return subprocess.run(args,check=True,**kw)
run(['ssh',host,f'mkdir -p {remote}'])
# Upload branch-owned new names only; failed source versions may be replaced.
assert module in {'R1Z/SimCostWide5', 'R1Z/SimCostCollect5', 'R1Z/SimCostFormula5', 'R1Z/SimCostRetry5', 'R1Z/SimCostPass5Audit'}
run(['ssh',host,f'test ! -f /home/dombarker/project-offloads/aspis-joint-20261019/sources/{module}.lean || mkdir -p {remote}/snapshots/{attempt} && cp -p /home/dombarker/project-offloads/aspis-joint-20261019/sources/{module}.lean {remote}/snapshots/{attempt}/ 2>/dev/null || true'])
run(['scp',str(src),f'{host}:/home/dombarker/project-offloads/aspis-joint-20261019/sources/{module}.lean'])
run(['scp',str(sub),str(ev/'host-attempt.py'),str(ev/'run-joint.sh'),f'{host}:{remote}/'])
p=subprocess.run(['ssh',host,f'python3 {remote}/host-attempt.py {remote}/{sub.name}'],text=True,capture_output=True)
(ev/f'launcher-{attempt}.log').write_text(p.stdout+p.stderr);print(p.stdout+p.stderr)
run(['scp',f'{host}:{remote}/attempts.jsonl',str(ev/f'receipt-{attempt}.json')])
for kind in ['out','time']:
 run(['scp',f'{host}:/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/{kind}-{attempt}.log',str(ev)])
sys.exit(p.returncode)
