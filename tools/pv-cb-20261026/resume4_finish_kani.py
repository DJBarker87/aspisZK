"""Finish only the three remaining, distinct named gates, strictly serially.
Reservation refusals consume names, not gates; wait180s and use a fresh name.
Any compiler/proof failure other than timeout stops for manual inspection.
"""
from pathlib import Path
import subprocess,sys,json,time
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
runs=[('kani-resume4-power-canonical-word3','canonical_power26_word3',None),('kani-resume4-compress16-canonical','compress16_canonical_reference',223),('kani-resume4-pole1024','pole1024_reference',258)]
for name,harness,op in runs:
 if op:
  r=subprocess.run([sys.executable,str(root/'tools/pv-cb-20261026/precheck.py'),str(op),'resume4-finalgate'],cwd=root)
  if r.returncode:raise SystemExit('Sibling changed: stop this gate and inspect')
 for n in range(1,11):
  label=name+f'-{n:03}'
  local=ev/label;assert not local.exists(),'Never reuse a gate name'
  r=subprocess.run([sys.executable,str(root/'tools/pv-cb-20261026/resume4_kani.py'),label,harness],cwd=root)
  p=local/'collected-receipt.json'
  if p.exists() and json.loads(p.read_text()).get('attempt_charged'):
   if r.returncode not in (0,124):raise SystemExit('Actual failed gate: inspect before continuing')
   break
  if (local/'target.json').exists():raise SystemExit('Admitted run without complete receipt: inspect first')
  if n==10:raise SystemExit('Ten reservation refusals; compile-free review required')
  print(label,'uncharged refusal; wait180s before fresh name',flush=True)
  for _ in range(18):time.sleep(10)
 else:raise SystemExit('No admission')
print('All remaining gates receipted',flush=True)
