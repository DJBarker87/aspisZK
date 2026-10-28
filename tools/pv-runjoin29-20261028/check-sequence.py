"""Sequential focused proof targets; halt at any refusal or local error."""
from pathlib import Path
import subprocess,sys,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin29-20261028'
ids=list(range(38183,38194))+list(range(42300,42397))
for name in sys.argv[1:]:
 a=next(i for i in ids if not (E/f'used-{i}.json').exists())
 print('NEXT',a,name,flush=True)
 p=subprocess.run([sys.executable,str(Path(__file__).with_name('check.py')),str(a),'R1Z/'+name])
 if p.returncode:sys.exit(p.returncode)
