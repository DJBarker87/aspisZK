from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');tag='sdk-live-out-shared-goto-v4';P=H/'target/kani/x86_64-unknown-linux-gnu/debug/deps';matches=list(P.glob('*sdk_live_out_shared_1_v4*actual_sdk_out_contract.out'));assert len(matches)==1;program=matches[0]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=['/home/dombarker/.kani/kani-0.67.0/bin/cbmc','--show-goto-functions',str(program)]
(H/(tag+'-input.json')).write_text(json.dumps(dict(program_sha256=hashlib.sha256(program.read_bytes()).hexdigest(),command=cmd,qualification='Metadata inspection only; no solver proof credit.'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Inspect loops in the tiny failing unit-output contract; no solver','--',*cmd]))
