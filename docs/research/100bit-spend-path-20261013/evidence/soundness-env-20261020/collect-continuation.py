"""Download text evidence only; compiled objects and archives stay on the host."""
import subprocess,json
from pathlib import Path
D=Path(__file__).resolve().parent
for n in ['summary','roots-current','axioms-audit','coherence-final']:
 p=D/(n+'-phase1.json')
 if not p.exists():p.write_bytes((D/(n+'.json')).read_bytes())
if not (D/'status-before-continuation.jsonl').exists():(D/'status-before-continuation.jsonl').write_bytes((D/'status.jsonl').read_bytes())
remote='/home/dombarker/project-offloads/aspis-joint-20261019/evidence-S'
script='''from pathlib import Path
D=Path("'''+remote+'''")
fixed={'manifest-S.json','status.jsonl','attempts.jsonl','coherence-final.json','current-objects.json','collision-closures.json','run-S-env2.sh','source-archive-env2.json','retained-comppoly-inventory.json','audit-collision-repair-driver.py'}
for p in D.iterdir():
 if not p.is_file():continue
 n=p.name
 if n in fixed or n.startswith('continuation-') and p.suffix in {'.json','.jsonl','.log'} or n.startswith(('out-7','time-7','launcher-7')) and n.endswith('.log') or n.startswith('SoundnessClosureAudit') and n.endswith('.lean'):print(n)
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True,capture_output=True,check=True)
subprocess.run(['rsync','-a','--files-from=-','dombarker@100.108.41.90:'+remote+'/',str(D)+'/'],input=r.stdout,text=True,check=True)
print('collected',len(r.stdout.splitlines()),'text files')
