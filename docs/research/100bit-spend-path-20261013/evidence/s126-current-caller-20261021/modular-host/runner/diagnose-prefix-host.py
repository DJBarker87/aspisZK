#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');name='sdk-prefix-v6-short-unwind-diagnostic'
files=list((H/'target/kani').rglob('aspis_s126_sdk_prefix_boundary_v6-*.out'));files=[p for p in files if not p.name.endswith('.symtab.out')];assert len(files)==1,files
p=files[0];tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cmd=['timeout','60',str(tool),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','4','--sat-solver','cadical','--slice-formula','--unwinding-assertions',str(p),'--verbosity','8']
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(name+'-input.json')).write_text(json.dumps(dict(command=cmd,goto_sha256=sha(p),cbmc_sha256=sha(tool),qualification='Deliberately insufficient unwind4 diagnostic on the exact kept artifact, timeout60s. No accepted verification or source-correspondence result.'),indent=2)+'\n')
os.chdir(H)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=16','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),'Short-bound diagnostic: distinguish symbolic-execution and solving costs; not an accepted proof','--',*cmd]))
