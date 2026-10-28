"""Serial admitted attempts; no timeout retry or verdict-driven renaming."""
from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent
shapes=json.loads((E/'NCM_NATIVE_SHAPES.json').read_text())
for i,shape in enumerate(shapes):
 for j,side in enumerate(['positive','negative']):
  a=f'NCM_K{2*i+j+1:03}';harness=shape['module']+'::'+shape[side]
  p=E/a/'receipt.json'
  if p.exists():continue # recovery of terminal attempt, never launch again
  print(a,harness,flush=True)
  r=subprocess.run([sys.executable,str(E/'NCM_kani.py'),a,harness])
  if r.returncode:raise SystemExit('STOP own wrapper; read/recover, never resubmit '+a)
  rc=json.loads(p.read_text());out=(E/a/'stdout.log').read_text()
  if 'VERIFICATION:- SUCCESSFUL' in out:verdict='PASS'
  elif 'VERIFICATION:- FAILED' in out:verdict='FAIL'
  elif 'TIMEOUT' in out or rc['exit_status'] in [124,137]:verdict='TIMEOUT_OR_KILL'
  else:verdict='NO_VERDICT'
  with (E/'NCM_NATIVE_VERDICTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,shape=shape['shape'],side=side,harness=harness,verdict=verdict,exit=rc['exit_status']))+'\n')
  # A compiler/gate failure is not a native verdict. Repair own input first.
  if verdict=='NO_VERDICT':raise SystemExit('STOP inspect own input/gate failure '+a)
  print(a,verdict,flush=True)
