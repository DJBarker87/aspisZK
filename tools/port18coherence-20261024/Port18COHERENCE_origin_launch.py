#!/usr/bin/env python3
import pathlib,subprocess,shlex
R=pathlib.Path(__file__).resolve().parents[2];T=R/'tools/port18coherence-20261024';E=R/'evidence/port18coherence-20261024';H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-port18coherence-20261024';a='lean-029'
files=[a+'.json','Port18COHERENCE_origins.py','origin-input.json','Port18COHERENCE_admission.py','Port18COHERENCE_run_host.py']
subprocess.run(['scp','-q',*[str(T/f) for f in files],H+':'+B+'/'],check=True)
s=f'python3 Port18COHERENCE_admission.py > {a}-before.json && python3 Port18COHERENCE_admission.py > {a}-go.json && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port18COHERENCE_run_host.py {a}.json'
p=subprocess.run(['ssh',H,'cd '+B+' && flock /tmp/aspis-r0-lean.lock sh -c '+shlex.quote(s)],capture_output=True,text=True)
(E/(a+'-launcher.log')).write_text(p.stdout+p.stderr)
for f in [a,a+'-before.json',a+'-go.json','original-root-objects.json']:
 subprocess.run(['scp','-qr',H+':'+B+'/'+f,str(E)],check=True)
print(p.stdout,p.stderr);raise SystemExit(p.returncode)
