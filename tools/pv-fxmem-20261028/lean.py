"""Submit the focused counterexample to the unchanged shared Env-J launcher."""
from pathlib import Path
import json,subprocess,hashlib,re,shlex,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
pre=json.loads((E/'PREFLIGHT.json').read_text());assert pre['ok']
n=int(sys.argv[1]) if len(sys.argv)>1 else 35500
assert 35500 <= n < 35597
m='R1Z/PV_FXM_DropCounterexample'
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads';D=B+'/codex-pv-fxmem-20261028'
G=B+'/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
sha=hashlib.sha256(p.read_bytes()).hexdigest();dep=next(x for x in pre['external'] if x['module']=='Init')
fp=hashlib.sha256(json.dumps(dep,sort_keys=True).encode()).hexdigest()
meta=dict(id=n,module=m,source_sha256=sha,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],cwd=R,text=True).strip(),dependencies={'Init':dep},deps_fingerprint=fp)
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n')
(E/f'{n}-source.lean.txt').write_bytes(p.read_bytes())
# Admission before uploading any source; both exit status and allowed:true.
code=f"mkdir -p {D}/runs/{n}; python3 {G}/reservation.py {D}/runs/{n}/admission-before.json > {D}/runs/{n}/reservation.log 2>&1; result=$?; cat {D}/runs/{n}/admission-before.json; exit $result"
r=subprocess.run(['ssh',H,code],text=True,capture_output=True)
(E/f'{n}-admission.json').write_text(r.stdout);(E/f'{n}-admission-stderr.log').write_text(r.stderr)
if r.returncode!=0:print(r.stderr);raise SystemExit(r.returncode)
assert json.loads(r.stdout)['allowed'] is True
r=subprocess.run(['scp','-q',str(p),H+':'+B+'/aspis-joint-20261019/sources/'+m+'.lean'])
if r.returncode:raise SystemExit(r.returncode)
command=[B+'/r1-privacy-build-integration-20261019/tools/run-joint.sh',str(n),m,'J','7000','8',fp]
(E/f'{n}-command.json').write_text(json.dumps(command)+'\n')
r=subprocess.run(['ssh',H,shlex.join(command)],text=True,capture_output=True)
(E/f'{n}-launcher.log').write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr)
print('launcher_transport_exit',r.returncode)
# A transport failure after submission is recovered read-only, never resubmitted.
if r.returncode:raise SystemExit(r.returncode)
