"""Task invocation of unchanged lead-owned runners; no runner modifications."""
import json,subprocess,sys,shlex,time
from pathlib import Path
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-cx-walker-cache-20261102'
a,mod=sys.argv[1:3];agg='--agg16' in sys.argv
# Conservative shared admission reserves 16 GiB even for an 8 GiB focused scope.
for retry in range(11):
 cmd=f'python3 {D}/reservation_agg16.py {D}/{a}-reservation-{retry}.json > {D}/{a}-barrier-{retry}.log 2>&1'
 r=subprocess.run(['ssh',H,cmd])
 subprocess.run(['scp','-q',f'{H}:{D}/{a}-reservation-{retry}.json',f'{H}:{D}/{a}-barrier-{retry}.log',str(E)],check=True)
 admission=json.loads((E/f'{a}-reservation-{retry}.json').read_text())
 with (E/'NEP_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,event='admission',exit=r.returncode,retry=retry,receipt=f'{a}-reservation-{retry}.json'))+'\n')
 if r.returncode==0 and admission.get('allowed') is True:break
 if r.returncode!=78:sys.exit('Reservation failure')
 if retry==10:sys.exit('Reservation refused ten retries')
 time.sleep(180)
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
sources=[mod+'.lean']; paths=D+':'+D+'/objects:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'
if agg:paths=D+':'+D+'/objects:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'
cfg=dict(kind='lean',module=mod,attempt=a,sources=sources,env={'LEAN_PATH':paths},timeout=600,command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M15000' if agg else '-M7000','-DElab.async=false','-o',mod+'.olean',mod+'.lean'],source_revision=rev,source_tree_dirty=True,deps_fingerprint={'scope':'NEP task private cache; final objects copied and hash verified from read-only NDR cohort'},expected_time='module import and raw dependency traversal; no arithmetic reduction',reservation_retries=retry)
if mod=='NEP_Driver':cfg['command']=cfg['command'][:6]+['--run',mod+'.lean','final' if agg else 'fixtures' if '--fixtures' in sys.argv else 'small']
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp','-q',str(E/(a+'.json')),*[str(E/s) for s in sources],H+':'+D+'/'],check=True)
runner='S2W_lean_host_agg16.py' if agg else 'S2W_lean_host.py'
cmd=f'cd {D} && systemd-run --user --scope -p MemoryHigh={"14G" if agg else "6G"} -p MemoryMax={"16G" if agg else "8G"} -p MemorySwapMax=0 -p TasksMax=64 python3 {runner} {a}.json'
r=subprocess.run(['ssh',H,cmd],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{H}:{D}/{a}',str(E)],check=True)
with (E/'NEP_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,event='scope',exit=r.returncode,agg16=agg,receipt=a+'/receipt.json'))+'\n')
print(r.stdout,r.stderr);sys.exit(r.returncode)
