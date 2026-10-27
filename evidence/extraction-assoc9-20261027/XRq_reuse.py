from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
mods=json.loads((E/'XRq_reuse.json').read_text())
for i,(m,s) in enumerate(mods.items(),1):
 a=f'XRq_L{i:03}'
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'XRq_attempt.py'),a,s,m],capture_output=True,text=True)
 print(a,m,r.stdout[-350:],r.stderr[-300:],flush=True)
 if r.returncode or not (E/a/'receipt.json').exists() or json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP prerequisite')
