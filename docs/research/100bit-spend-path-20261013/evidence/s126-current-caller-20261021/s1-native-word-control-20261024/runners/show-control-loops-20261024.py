#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');W=H/'s1-control-loop-inventory-20261024';W.mkdir(exist_ok=False)
files=list((H/'target/kani/x86_64-unknown-linux-gnu/debug/deps').glob('*49original_and_owned_ordered_normal_return_contract.out'));assert len(files)==1;binary=files[0]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(W/'admission.json')],check=True,stdout=subprocess.DEVNULL)
snap=subprocess.check_output(['python3','/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py'],text=True);(W/'global-admission.json').write_text(snap);m=json.loads(snap);G=2**30;assert m['effective_sum_bytes']+2*G<=48*G and m['MemAvailable_kB']*1024>=4*G
os.environ['PATH']='/home/dombarker/.cargo/bin:/usr/bin:/bin';tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cmd=[str(tool),'--show-loops',str(binary)];(W/'input.json').write_text(json.dumps(dict(command=cmd,binary_sha256=sha(binary),binary_parent_attempt='s1-claim-ordered-tape-v1-sat-v2',tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),qualification='Read-only retained GOTO control inventory, not a proof. Binary hash only; no binary distribution.'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(W/'attempt'),'Read-only original/reference GOTO loop inventory; no solver or source change','--',*cmd]))
