"""Sequential focused checks; stop at the first failure or refusal."""
from pathlib import Path
import subprocess,json,sys
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
n=int(sys.argv[1])
for m in sys.argv[2:]:
 used=sum(1 for p in ev.glob('38*.json') if p.stem.isdigit() and 38300<=int(p.stem)<=38599)
 assert used<97,'Final three attempts are reserved for joint audits'
 with (ev/f'{n}-queue-transport.log').open('w') as f:
  subprocess.run([sys.executable,str(root/'tools/pv-cb-20261026/resume4_lean.py'),str(n),m],stdout=f,stderr=subprocess.STDOUT)
 p=ev/f'{n}.json'
 if not p.exists():raise SystemExit(f'{n} preflight/refusal; inspect queue transport and consume fresh next ID')
 r=json.loads(p.read_text());print(n,m,'exit',r['exit'],flush=True)
 if r['exit']:raise SystemExit('Repair this changed target before any dependent check')
 n+=1
print('next unused ID',n)
