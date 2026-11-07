"""Serial own attempts, never retry an existing receipt or failed shape."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a in sys.argv[1:]:
 r=subprocess.run([sys.executable,str(E/'NLZ_run.py'),a])
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: recover read-only, do not resubmit '+a)
 x=json.loads(p.read_text())
 if a.startswith('NLZ_K'):
  text=(p.parent/'stdout.log').read_text();control=x['module'].endswith('_control')
  verdict='PASS'if r.returncode==0 and'VERIFICATION:- SUCCESSFUL'in text else'CONTROL_FAIL'if control and('Failed Checks: assertion failed: !good'in text or 'Failed Checks: assertion failed: good && log.phase'in text) and'CBMC timed out'not in text else'TIMEOUT'if'CBMC timed out'in text else'UNEXPECTED'
  with(E/'NLZ_NATIVE_CLASSIFICATION.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,verdict=verdict,control=control,exit=r.returncode))+'\n')
  if verdict not in ['PASS','CONTROL_FAIL']:raise SystemExit('Isolate changed shape before continuing: '+a+' '+verdict)
 elif r.returncode:raise SystemExit('Inspect changed proof before continuing: '+a)
