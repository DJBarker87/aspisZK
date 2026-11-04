from pathlib import Path
import subprocess,sys,os
E=Path(__file__).resolve().parent
jobs=[(38+(call-1)*2+inv,call,inv) for call in range(1,6) for inv in range(2)]
for i,call,inv in jobs:
  env=dict(os.environ,NFW_CALL=str(call))
  if inv:env['NFW_INVERT']='1'
  r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_K{i:03}','kani','verifier::NFW_prepared::prepared_facet16'],env=env,capture_output=True,text=True)
  (E/f'NFW_K{i:03}-queue.log').write_text(r.stdout+r.stderr)
  print(i,call,r.returncode,r.stdout[:350],flush=True)
  p=E/f'NFW_K{i:03}/stdout.log';out=p.read_text() if p.exists() else ''
  if r.returncode!=inv or 'timed out' in out.lower() or (inv and 'Failed Checks:' not in out):sys.exit(r.returncode or 2)
