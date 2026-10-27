"""Sequential focused root-cell checks, stopping on every refusal or error."""
from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027'
for cell in range(int(sys.argv[1]),int(sys.argv[2])+1):
 attempt=max(int(p.stem.split('-')[1]) for p in E.glob('used-*.json'))+1
 module=f'R1Z/PV_RunJoin_RootModelCell{cell:02d}'
 p=subprocess.run([sys.executable,str(R/'tools/pv-runjoin12-20261027/check.py'),str(attempt),module],capture_output=True,text=True)
 (E/f'cell-driver-{attempt}.log').write_text(p.stdout+p.stderr)
 print('\n'.join(line for line in p.stdout.splitlines() if line.startswith(('RECEIPT','RESERVATION','LAUNCH'))),flush=True)
 if p.returncode:print('Stopped on nonzero result; inspect before another launch',flush=True);sys.exit(p.returncode)
