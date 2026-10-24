#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');W=H/'s1-control-symex-diagnostic-20261024';W.mkdir(exist_ok=False)
files=list((H/'target/kani/x86_64-unknown-linux-gnu/debug/deps').glob('*49original_and_owned_ordered_normal_return_contract.out'));assert len(files)==1;binary=files[0]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(W/'admission.json')],check=True,stdout=subprocess.DEVNULL)
snap=subprocess.check_output(['python3','/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py'],text=True);(W/'global-admission.json').write_text(snap);m=json.loads(snap);G=2**30;assert m['effective_sum_bytes']+3*G<=48*G and m['MemAvailable_kB']*1024>=5*G
os.environ['PATH']='/home/dombarker/.cargo/bin:/usr/bin:/bin';tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cmd=['timeout','20',str(tool),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--slice-formula','--unwinding-assertions','--verbosity','9',str(binary)];(W/'input.json').write_text(json.dumps(dict(command=cmd,binary_sha256=sha(binary),binary_parent_attempt='s1-claim-ordered-tape-v1-sat-v2',tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),qualification='Read-only retained GOTO control inventory, not a proof. Binary hash only; no binary distribution.'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=2G','-p','MemoryMax=3G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(W/'attempt'),'Twenty-second retained GOTO symbolic-execution diagnostic; no proof claim or source change','--',*cmd]))
