"""Submit the focused counterexample to the unchanged shared Env-J launcher."""
from pathlib import Path
import json,subprocess,hashlib,re,shlex,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
pre=json.loads((E/'PREFLIGHT.json').read_text());assert pre['ok']
n=int(sys.argv[1]) if len(sys.argv)>1 else 35500
assert 35500 <= n < 35597
m=sys.argv[2] if len(sys.argv)>2 else 'R1Z/PV_FXM_DropCounterexample'
assert m.startswith('R1Z/PV_FXM_')
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
imports=re.findall(r'^import (\S+)',p.read_text(),re.M)
carrier = imports != ['Init']
if carrier:
 carrier_path=E/('CARRIER-RESERVE-PREFLIGHT.json' if 'R1Z.PDict_ReserveErrorSource' in imports else 'CARRIER-FUNS-PREFLIGHT.json' if 'R1Z.ProverRwFullFuns' in imports else 'CARRIER-PREFLIGHT.json')
 pre=json.loads(carrier_path.read_text());assert pre['ok']
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads';D=B+'/codex-pv-fxmem-20261028'
G=B+'/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
def prelaunch(args):
 for retry in range(1,11):
  r=subprocess.run(args,text=True,capture_output=True)
  if r.returncode!=255:return r
  with (E/'transport.jsonl').open('a') as f:f.write(json.dumps(dict(operation='precompiler admission/upload',id=n,exit=255,error=r.stderr,retry=retry,epoch=time.time()))+'\n')
  if retry<10:time.sleep(60)
 return r

sha=hashlib.sha256(p.read_bytes()).hexdigest();dep=pre if carrier else next(x for x in pre['external'] if x['module']=='Init')
if carrier:
 dep={'carrier_preflight_sha256':hashlib.sha256(carrier_path.read_bytes()).hexdigest(),'project':pre['project'],'owned_drop':json.loads((E/'35503-submission.json').read_text())}
 for owned in imports:
  if owned=='R1Z.PV_FXM_ZeroWorld':
   dep['owned_zero']=json.loads((E/'35508-submission.json').read_text())
  if owned=='R1Z.PV_FXM_ReserveWorld':
   dep['owned_reserve']=json.loads((E/'35515-submission.json').read_text())
  if owned=='R1Z.PV_FXM_ZeroSelected':
   dep['owned_zero_selected']=json.loads((E/'35510-submission.json').read_text())
fp=hashlib.sha256(json.dumps(dep,sort_keys=True).encode()).hexdigest()
meta=dict(id=n,module=m,source_sha256=sha,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],cwd=R,text=True).strip(),dependencies=dep,deps_fingerprint=fp)
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n')
(E/f'{n}-source.lean.txt').write_bytes(p.read_bytes())
# Admission before uploading any source; both exit status and allowed:true.
code=f"mkdir -p {D}/runs/{n}; python3 {G}/reservation.py {D}/runs/{n}/admission-before.json > {D}/runs/{n}/reservation.log 2>&1; result=$?; cat {D}/runs/{n}/admission-before.json; exit $result"
r=prelaunch(['ssh',H,code])
(E/f'{n}-admission.json').write_text(r.stdout);(E/f'{n}-admission-stderr.log').write_text(r.stderr)
if r.returncode!=0:print(r.stderr);raise SystemExit(r.returncode)
assert json.loads(r.stdout)['allowed'] is True
r=prelaunch(['scp','-q',str(p),H+':'+B+'/aspis-joint-20261019/sources/'+m+'.lean'])
if r.returncode:raise SystemExit(r.returncode)
command=[B+'/r1-privacy-build-integration-20261019/tools/run-joint.sh',str(n),m,'J','7000','8',fp]
(E/f'{n}-command.json').write_text(json.dumps(command)+'\n')
r=subprocess.run(['ssh',H,shlex.join(command)],text=True,capture_output=True)
(E/f'{n}-launcher.log').write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr)
print('launcher_transport_exit',r.returncode)
# A transport failure after submission is recovered read-only, never resubmitted.
if r.returncode:raise SystemExit(r.returncode)
