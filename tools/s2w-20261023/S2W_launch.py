#!/usr/bin/env python3
"""Launch one admitted, capped host extraction; collect full receipts."""
import pathlib,subprocess,sys,json,shlex
B=pathlib.Path(__file__).resolve().parent;R=B.parents[1];E=R/'evidence/s2w-20261023'
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-cx-s2w-20261023'
c=pathlib.Path(sys.argv[1]);a=json.loads(c.read_text())['attempt']
# Same populated-scope reservation policy as the existing S2Z launcher.
s=(B/'S2W_compile.py').read_text();admission=s.split("admission='''",1)[1].split("'''",1)[0]
r=subprocess.run(['ssh',H,'python3','-c',shlex.quote(admission)],check=True,capture_output=True,text=True)
(E/f'{a}-reservation.json').write_text(r.stdout)
subprocess.run(['scp','-q',str(c),str(B/'S2W_run_host.py'),H+':'+D+'/'],check=True)
cmd=f'cd {D} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {c.name}'
r=subprocess.run(['ssh',H,cmd],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',H+':'+D+'/'+a,str(E)],check=True)
print(r.stdout);print(r.stderr);sys.exit(r.returncode)
