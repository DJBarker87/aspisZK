#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,sys,time,hashlib,os
D=Path('/home/dombarker/project-offloads/codex-pv-l3a-20261029')
S=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py')
if len(sys.argv)==1:
    # Admission and launch deliberately in the SAME process/command (D410).
    with (D/'native01-admission.log').open('w') as log:
        p=subprocess.run(['python3',str(S),str(D/'native01-admission.json')],stdout=log,stderr=subprocess.STDOUT)
    if p.returncode:sys.exit(p.returncode)
    if json.loads((D/'native01-admission.json').read_text()).get('allowed') is not True:sys.exit(78)
    sys.exit(subprocess.run(['systemd-run','--user','--scope','--unit=pv-l3a-native01','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'PV_L3A_launch.py'),'inside']).returncode)
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().strip().split('::')[-1])
limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64'])),limits
cmd=['python3',str(D/'PV_L3A_audit.py'),str(D),'/home/dombarker/project-offloads/codex-pv-rdea-20261028/client-target/release/devnet_spend']
t=time.monotonic()
with (D/'native01-output.log').open('w') as log:
    p=subprocess.run(['/usr/bin/time','-v','-o',str(D/'native01-time.log'),*cmd],stdout=log,stderr=subprocess.STDOUT)
r=dict(target='V373 linked-image symbol/GOT call inventory and conservative taint scan',command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-t,cgroup=str(cg),limits=limits,peak_cgroup_bytes=(cg/'memory.peak').read_text().strip(),swap_current_bytes=(cg/'memory.swap.current').read_text().strip(),source_revision='42760700cbae39587de93f520aed51618e13ef0a',print_axioms='N/A: no Lean theorem',phase='finite static disassembly and taint analysis; no compilation/proof generation',script_sha256=hashlib.sha256((D/'PV_L3A_audit.py').read_bytes()).hexdigest(),launcher_sha256=hashlib.sha256((D/'PV_L3A_launch.py').read_bytes()).hexdigest())
(D/'native01-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));sys.exit(p.returncode)
