"""Replay missing unchanged inputs serially through the existing invocation."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
pairs=json.loads((E/'XRv_dependency-order.json').read_text())
pairs=[(m,s) for m,s in pairs if m!='XRt_RootAudit']
mods=dict(pairs);done=set();order=[]
def visit(m):
 if m in done:return
 done.add(m)
 for line in Path(mods[m]).read_text().splitlines():
  if line.startswith('import '):
   for d in line[7:].split():
    if d in mods:visit(d)
 order.append((m,mods[m]))
for m in mods:visit(m)
(E/'XRv_restore-order.json').write_text(json.dumps(order,indent=2)+'\n')
for i,(m,s) in enumerate(order,6):
 a=f'XRv_L{i:03}'
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'XRv_attempt.py'),a,s,m],capture_output=True,text=True)
 print(a,m,r.stdout[-400:],r.stderr[-200:],flush=True)
 if r.returncode or not (E/a/'receipt.json').exists() or json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP prerequisite')
