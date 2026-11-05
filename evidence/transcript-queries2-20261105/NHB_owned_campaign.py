from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
for n in range(8,23):
 for invert in [False,True]:
  number=22+2*(n-8)+int(invert);a=f'NHB_K{number:03}'
  if (E/a).exists():raise RuntimeError('Existing attempt, never resubmit '+a)
  env=dict(os.environ)
  if invert:env['NHB_INVERT']='1'
  with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NHB_run.py'),a,'kani',f'r0_transcript::NHB_harness::NHB_contains_{n}_contract'],env=env,stdout=f,stderr=subprocess.STDOUT)
  p=E/a/'receipt.json';assert p.exists(),a+' no receipt; recover only'
  rc=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text()
  intended=(r.returncode!=0 and 'Failed Checks: |out| *out ==' in raw and '1 of ' in raw and 'timed out' not in raw and 'unwinding assertion' not in raw and 'CBMC failed' not in raw)
  good=intended if invert else r.returncode==0 and 'VERIFICATION:- SUCCESSFUL' in raw
  print(json.dumps(dict(attempt=a,length=n,invert=invert,exit=r.returncode,expected_verdict=good,wall=rc['wall_seconds'])),flush=True)
  if not good:sys.exit(1)
