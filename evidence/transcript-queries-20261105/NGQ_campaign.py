"""Serial owned campaign; admission and per-attempt evidence remain in NGQ_run."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for k in range(1,8):
 for invert in [False,True]:
  a='NGQ_K'+str(10+2*(k-1)+int(invert)).zfill(3)
  env=dict(os.environ,NGQ_VERIFIER='1')
  if invert:env['NGQ_INVERT']='1'
  r=subprocess.run(['python3',str(E/'NGQ_run.py'),a,'kani',f'transcript::NGQ_pairs::NGQ_pair{k}'],env=env,capture_output=True,text=True)
  (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
  p=E/a/'receipt.json'
  if not p.exists():print(a,'NO RECEIPT; STOP',flush=True);break
  rc=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text()
  verdict='SUCCESSFUL' if 'VERIFICATION:- SUCCESSFUL' in raw else 'FAILED' if 'VERIFICATION:- FAILED' in raw else 'OTHER'
  print(a,verdict,rc['wall_seconds'],rc['peak_rss_kib'],flush=True)
  if verdict!=('FAILED' if invert else 'SUCCESSFUL'):raise SystemExit('STOP unexpected verdict; isolate before any retry')
