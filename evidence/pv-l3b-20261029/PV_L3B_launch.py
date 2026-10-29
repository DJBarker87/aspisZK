from pathlib import Path
import os,sys,json,subprocess,time,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-l3b-20261029')
R=D.parent/'codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
n=sys.argv[1]
if len(sys.argv)==2:
    with (D/f'{n}-admission.log').open('w') as f:
        p=subprocess.run(['python3',str(R),str(D/f'{n}-admission.json')],stdout=f,stderr=subprocess.STDOUT)
    if p.returncode: sys.exit(p.returncode)
    if json.loads((D/f'{n}-admission.json').read_text()).get('allowed') is not True: sys.exit(78)
    sys.exit(subprocess.run(['systemd-run','--user','--scope','-q',f'--unit=pv-l3b-{n}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'PV_L3B_launch.py'),n,'inside']).returncode)
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().strip().split('::')[-1])
limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert list(limits.values())==['6442450944','8589934592','0','64']
cmd=['python3',str(D/f'PV_L3B_{n}.py')]
t=time.monotonic()
with (D/f'{n}-output.log').open('w') as f:
    p=subprocess.run(['/usr/bin/time','-v','-o',str(D/f'{n}-time.log'),*cmd],stdout=f,stderr=subprocess.STDOUT)
r=dict(command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-t,limits=limits,peak_cgroup_bytes=(cg/'memory.peak').read_text().strip(),swap_bytes=(cg/'memory.swap.current').read_text().strip(),source_revision='b3a9a2842f',print_axioms='N/A native analysis/build',script_sha256=hashlib.sha256((D/f'PV_L3B_{n}.py').read_bytes()).hexdigest())
(D/f'{n}-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));sys.exit(p.returncode)
