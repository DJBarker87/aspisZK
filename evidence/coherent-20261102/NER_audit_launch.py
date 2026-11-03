"""Task inputs to unmodified lead runners. No build infrastructure changes."""
import json, subprocess, sys, time
from pathlib import Path
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
D='/home/dombarker/project-offloads/codex-cx-coherent-cache-20261102'
LEAD='/home/dombarker/project-offloads/codex-cx-fixture-cache-20261027'
SEED='/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028'
SYS='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a='NER_A901';mod='NDR_CombinedAudit';agg=True
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
cmd=['python3','NER_audit.py']
cfg=dict(kind='lean',module=['RPx_Deployed','NDR_CombinedAudit'],attempt=a,sources=['NER_audit.py','NER_FinalDriverV2.lean','NER_PREAGG_OBJECTS_A901.jsonl'],env={'LEAN_PATH':paths},timeout=1200,command=cmd,source_revision=rev,source_tree_dirty=True,deps_fingerprint={'scope':'All 1387 required objects rebuilt; no unchanged model compilation; exact selected and original object pins verified before/after runtime audit'},expected_time='One private whole-closure import; corrected stable-unique import comparison, all-own-declaration active-kernel scan, two hardened raw walks',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp','-q',str(E/(a+'.json')),str(E/'NER_audit.py'),str(E/'NER_FinalDriverV2.lean'),str(E/'NER_PREAGG_OBJECTS_A901.jsonl'),H+':'+D+'/'],check=True)
runner='S2W_run_host_agg16.py'
r=subprocess.run(['ssh',H,f'cd {D} && systemd-run --user --scope -p MemoryHigh={"14G" if agg else "6G"} -p MemoryMax={"16G" if agg else "8G"} -p MemorySwapMax=0 -p TasksMax=64 python3 {runner} {a}.json'],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{H}:{D}/{a}',str(E)],check=True)
with (E/'NER_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,event='scope',exit=r.returncode,agg16=agg,receipt=a+'/receipt.json'))+'\n')
print(r.stdout,r.stderr);sys.exit(r.returncode)
