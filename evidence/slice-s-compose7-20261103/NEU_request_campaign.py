from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;n=int(sys.argv[1])
for shape in ['prefix','payment_carrier','profile','release','pool_program','postguard']:
 for mode in ['positive','negative']:
  a=f'NEU_K{n:03}';n+=1
  subprocess.run([sys.executable,str(E/'NEU_prepare_request.py'),shape,mode],check=True)
  (E/(a+'-request.json')).write_bytes((E/'NEU_REQUEST_CURRENT.json').read_bytes())
  r=subprocess.run([sys.executable,str(E/'NEU_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEU_request::request_slice'],capture_output=True,text=True)
  print(a,shape,mode,r.stdout[-1100:],r.stderr,flush=True)
  t=(E/a/'stdout.log').read_text()
  if 'timed out' in t.lower():
   print('EXCLUDED timeout; no unchanged retry',flush=True);break
  if ('VERIFICATION:- SUCCESSFUL' in t)!=(mode=='positive') or (mode=='negative' and 'Failed Checks:' not in t):raise SystemExit('STOP own campaign requires source/error inspection')
