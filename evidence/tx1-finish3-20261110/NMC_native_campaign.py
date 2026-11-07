"""Owned serial campaign. A failed shape is retained, never retried here."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
pairs=['map_owner','map_claims','map_alpha','map_extra','map_transcript','map_challenges','map_allocator','map_rest']
for n,name in enumerate(pairs):
 for bad in [False,True]:
  a=f'NMC_K{5+2*n+int(bad):03}'
  h='NMC_program::'+name+('_control' if bad else '_cut')
  subprocess.run([sys.executable,str(E/'NMC_kconfig.py'),a,h],check=True)
  r=subprocess.run([sys.executable,str(E/'NMC_run.py'),a])
  p=E/a/'receipt.json'
  if not p.exists():sys.exit('Missing receipt; do not submit another scope')
  x=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
  timeout='timed out' in log or x['exit_status']==124
  expected=x['exit_status']==(1 if bad else 0) and not timeout
  with (E/'NMC_NATIVE_VERDICTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,harness=h,expected_verdict=expected,timeout=timeout,exit_status=x['exit_status']))+'\n')
  if not expected:sys.exit('Review changed-shape/independent-member continuation before next launch')
