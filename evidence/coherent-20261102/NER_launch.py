"""Task inputs to unmodified lead runners. No build infrastructure changes."""
import json, subprocess, sys, time
from pathlib import Path
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
D='/home/dombarker/project-offloads/codex-cx-coherent-cache-20261102'
LEAD='/home/dombarker/project-offloads/codex-cx-fixture-cache-20261027'
SEED='/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028'
SYS='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,mod=sys.argv[1:3]
runargs=sys.argv[3:]
agg='--agg16' in runargs
if agg:runargs.remove('--agg16')
for retry in range(11):
 r=subprocess.run(['ssh',H,f'python3 {LEAD}/reservation_agg16.py {D}/{a}-reservation-{retry}.json > {D}/{a}-barrier-{retry}.log 2>&1'])
 subprocess.run(['scp','-q',f'{H}:{D}/{a}-reservation-{retry}.json',f'{H}:{D}/{a}-barrier-{retry}.log',str(E)],check=True)
 admission=json.loads((E/f'{a}-reservation-{retry}.json').read_text())
 with (E/'NER_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,event='admission',exit=r.returncode,retry=retry,receipt=f'{a}-reservation-{retry}.json'))+'\n')
 if r.returncode==0 and admission.get('allowed') is True:break
 if r.returncode!=78:sys.exit('Reservation failure')
 if retry==10:sys.exit('Reservation refused ten retries')
 for _ in range(3):time.sleep(60)
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
paths=f'{D}:{D}/objects:{SEED}:{SEED}/objects:{SYS}/lib/lean'
cmd=[f'{SYS}/bin/lake','env','lean','-j1','-M15000' if agg else '-M7000','-DElab.async=false']
cmd+=['--run',mod+'.lean',*runargs] if runargs else ['-o',mod+'.olean',mod+'.lean']
cfg=dict(kind='lean',module=mod,attempt=a,sources=[mod+'.lean'],env={'LEAN_PATH':paths},timeout=600,command=cmd,source_revision=rev,source_tree_dirty=True,deps_fingerprint={'scope':'Own overlay, read-only NDR cohort; serialized closure pinned separately'},expected_time='serialized module inspection or single named module compilation; no dependency build',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp','-q',str(E/(a+'.json')),str(E/(mod+'.lean')),H+':'+D+'/'],check=True)
runner='S2W_lean_host_agg16.py' if agg else 'S2W_lean_host.py'
r=subprocess.run(['ssh',H,f'cd {D} && systemd-run --user --scope -p MemoryHigh={"14G" if agg else "6G"} -p MemoryMax={"16G" if agg else "8G"} -p MemorySwapMax=0 -p TasksMax=64 python3 {runner} {a}.json'],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{H}:{D}/{a}',str(E)],check=True)
with (E/'NER_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,event='scope',exit=r.returncode,agg16=agg,receipt=a+'/receipt.json'))+'\n')
print(r.stdout,r.stderr);sys.exit(r.returncode)
