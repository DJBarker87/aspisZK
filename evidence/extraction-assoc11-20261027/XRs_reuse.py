from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for i,(m,s) in enumerate(json.loads((E/'XRs_reuse.json').read_text()).items(),39):
 a=f'XRs_L{i:03}'
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'XRs_attempt.py'),a,s,m],capture_output=True,text=True)
 print(a,m,r.stdout[-240:],r.stderr[-200:],flush=True)
 if r.returncode or not (E/a/'receipt.json').exists() or json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP prerequisite')
