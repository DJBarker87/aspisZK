from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
labels=['NMP_L268','NMP_L269','NMP_L270','NMP_L271']+[f'NMP_L{171+i:03d}' for i in range(97)]
for a in labels:
 assert not (E/a/'receipt.json').exists(),'Never resubmit '+a
 r=subprocess.run([sys.executable,str(E/'NMP_run.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
