"""Job-private invocation/receipt wrapper; shared launchers stay unchanged."""
from pathlib import Path
import os,sys,json,subprocess,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028')
G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy')
def run(label,cmd,note,extra=None):
 O=H/label;O.mkdir(exist_ok=False)
 cooldown=H/"admission-not-before.json"
 if cooldown.exists() and time.time()<json.loads(cooldown.read_text())["epoch"]:
  (O/"cooldown-refusal.json").write_text(cooldown.read_text());return 78
 env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'target'),PV_REV=(H/'revision').read_text().strip())
 env.update(extra or {})
 (O/'target.json').write_text(json.dumps(dict(command=cmd,revision=env['PV_REV'],expected_time=note),indent=2))
 with (O/'reservation.log').open('w') as f:r=subprocess.run(['python3',str(G/'reservation.py'),str(O/'reservation.json')],stdout=f,stderr=subprocess.STDOUT,env=env)
 if not (O/'reservation.json').exists():raise SystemExit('reservation JSON missing; transient scanner failure: see '+str(O/'reservation.log'))
 admission=json.loads((O/'reservation.json').read_text())
 if r.returncode!=0 or admission.get('allowed') is not True:
  (O/'refusal.json').write_text(json.dumps(dict(exit=r.returncode,allowed=admission.get('allowed'),charged_lean_attempts=0,scope_started=False,wait_seconds_required=180)))
  cooldown.write_text(json.dumps(dict(epoch=time.time()+180,reason="outside reservation refusal",label=label)))
  return 78
 scope=['systemd-run','--user','--scope','--unit=pv-b3p6-'+label,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'barrier.json'),'python3',str(H/'capped.py'),str(O/'receipt'),note,'--',*cmd]
 with (O/'scope.log').open('w') as f:r=subprocess.run(scope,cwd=H/'source',env=env,stdout=f,stderr=subprocess.STDOUT)
 if (O/'barrier.json').exists() and not (O/'receipt/receipt.json').exists():
  admission=json.loads((O/'barrier.json').read_text())
  if admission.get('allowed') is not True:
   cooldown.write_text(json.dumps(dict(epoch=time.time()+180,reason='inside reservation refusal',label=label)));return 78
 return r.returncode
if __name__=='__main__':
 label=sys.argv[1];cmd=sys.argv[2:]
 sys.exit(run(label,cmd,'optimized Rust compilation; no proof generation or elimination',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}))
