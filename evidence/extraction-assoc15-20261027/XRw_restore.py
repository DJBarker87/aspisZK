"""Serial replay of only missing unchanged dependencies in the retained cache."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
pairs=json.loads((E/'XRw_dependency-order.json').read_text())
reused={r['module'] for r in json.loads((E/'XRw_reused-object-snapshot.json').read_text())}
start=5
for m,s in pairs:
 if m in reused:continue
 a=f'XRw_L{start:03}';start+=1
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'XRw_attempt.py'),a,s,m],capture_output=True,text=True)
 print(a,m,r.stdout[-700:],r.stderr[-200:],flush=True)
 if r.returncode or not (E/a/'receipt.json').exists() or json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP prerequisite')
