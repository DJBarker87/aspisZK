from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];T=Path(__file__).parent;E=R/'evidence/pv-runjoin58-20261029'
x=json.loads((E/'fixture-pins.json').read_text())
for a,m in enumerate(x['order'],68800):
 if (E/f'receipt-{a}.json').exists():
  assert json.loads((E/f'receipt-{a}.json').read_text())['accepted'];continue
 print('FIXTURE PREREQUISITE',a,m,flush=True)
 r=subprocess.run([sys.executable,str(T/'focused.py'),str(a),m])
 if r.returncode:sys.exit(r.returncode)
