from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i in range(277,281):
 a=f'NMP_L{i:03d}'
 assert not (E/a/'receipt.json').exists(),'Never resubmit '+a
 r=subprocess.run([sys.executable,str(E/'NMP_run.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
