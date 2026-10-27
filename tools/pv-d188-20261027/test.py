"""Use the standing private launcher unchanged except private source/object roots."""
import subprocess,sys,json,shlex,hashlib,re,time
from pathlib import Path
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-d188-20261027';host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads/codex-pv-d188-20261027'
a=int(sys.argv[1]);module=sys.argv[2];assert 28100<=a<=28299 and module.startswith('PV_D188_')
src=out/'tests'/(module+'.lean');assert src.exists()
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
r=ssh(f'python3 {gate} {base}/{a}-admission.json > {base}/{a}-reservation.log 2>&1; status=$?; cat {base}/{a}-reservation.log; exit $status')
(out/f'{a}-admission.log').write_text(r.stdout+r.stderr)
try:allowed=json.loads(r.stdout)['allowed'] is True
except Exception:allowed=False
if r.returncode!=0 or not allowed:
 (out/f'{a}-refusal.json').write_text(json.dumps(dict(exit=r.returncode,charged=False,output=r.stdout+r.stderr),indent=2)+'\n');sys.exit(78)
r=ssh(f"mkdir -p {base}/sources {base}/objects; sed 's@codex-pv-op134-20261027@codex-pv-d188-20261027@g' /home/dombarker/project-offloads/codex-pv-op134-20261027/run-joint.sh > {base}/run-joint.sh; chmod +x {base}/run-joint.sh")
assert r.returncode==0,r.stderr
# Isolated import-priority correction after 28100: use retained J objects first.
code="""from pathlib import Path
import json
base=Path('/home/dombarker/project-offloads/codex-pv-d188-20261027')
e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
e['LEAN_PATH']=str(base/'objects')+':/home/dombarker/project-offloads/aspis-joint-20261019/objects:'+e['LEAN_PATH']
(base/'env-J.json').write_text(json.dumps(e,indent=2))
p=base/'run-joint.sh';s=p.read_text();s=s.replace('ENVJ="$H/env/$E.json"','ENVJ="'+str(base/'env-J.json')+'"');p.write_text(s)
"""
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
subprocess.run(['scp',str(src),f'{host}:{base}/sources/{module}.lean'],check=True,capture_output=True)
# Record a real import/environment fingerprint for all subsequent tests.
imports=re.findall(r'^import (\S+)',src.read_text(),re.M)
code="""from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-pv-d188-20261027');e=json.loads((b/'env-J.json').read_text());r={}
for m in %r:
 for d in e['LEAN_PATH'].split(':'):
  p=Path(d)/(m.replace('.','/')+'.olean')
  if p.exists():r[m]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()};break
 else:r[m]='MISSING'
r['environment_sha256']=hashlib.sha256((b/'env-J.json').read_bytes()).hexdigest();print(json.dumps(r,sort_keys=True))
"""%imports
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
(out/f'{a}-imports.json').write_text(r.stdout)
fp=hashlib.sha256(r.stdout.encode()).hexdigest()
started=time.time();r=ssh(f'{base}/run-joint.sh {a} {module} J 7000 8 {fp}');wall=time.time()-started
(out/f'{a}-launcher.log').write_text(r.stdout+r.stderr)
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
for f in ['out','time','sha']:
 z=ssh(f'cat {T}/{f}-{a}.'+('txt' if f=='sha' else 'log'))
 (out/f'{a}-{f}.log').write_text(z.stdout+z.stderr)
s=(out/f'{a}-out.log').read_text();tm=(out/f'{a}-time.log').read_text();match=re.search(r'exit=(\d+)',s)
rec=dict(attempt=a,target=module,command=f'{base}/run-joint.sh {a} {module} J 7000 8 {fp}',exit=int(match[1]) if match else r.returncode,charged=bool(match),wall_seconds=wall,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),peak_rss_kib=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',tm),swaps=re.findall(r'Swaps: (\d+)',tm),print_axioms='N/A testing only; no theorem added',caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(out/f'{a}-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));print(s[-7000:]);sys.exit(rec['exit'])
