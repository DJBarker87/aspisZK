"""Sequential focused modules; stop on every refusal/error and inspect it."""
from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027'
for module in sys.argv[1:]:
 attempt=max(int(p.stem.split('-')[1]) for p in E.glob('used-*.json'))+1
 p=subprocess.run([sys.executable,str(R/'tools/pv-runjoin12-20261027/check.py'),str(attempt),'R1Z/'+module],capture_output=True,text=True)
 (E/f'module-driver-{attempt}.log').write_text(p.stdout+p.stderr)
 print('\n'.join(l for l in p.stdout.splitlines() if l.startswith(('LAUNCH','RECEIPT','RESERVATION'))),flush=True)
 if p.returncode:print(p.stdout[-2500:]+p.stderr[-1000:],flush=True);sys.exit(p.returncode)
