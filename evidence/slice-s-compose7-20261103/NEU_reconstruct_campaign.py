from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1]);shapes=sys.argv[2:]
for shape in shapes:
 for mode in ['positive','negative']:
  a=f'NEU_K{n:03}';n+=1;assert n<=131
  subprocess.run([sys.executable,str(E/'NEU_prepare_reconstruct.py'),shape,mode],check=True)
  (E/(a+'-reconstruct.json')).write_bytes((E/'NEU_RECONSTRUCT_CURRENT.json').read_bytes())
  r=subprocess.run([sys.executable,str(E/'NEU_program_kani_run.py'),a,'kani','r1_pool_adapter::NEU_reconstruct::reconstruction_slice'],capture_output=True,text=True)
  print(a,shape,mode,r.stdout[-1000:],r.stderr,flush=True)
  t=(E/a/'stdout.log').read_text()
  if 'timed out' in t.lower():print('EXCLUDED timeout; split required; no retry',flush=True);raise SystemExit(2)
  if ('VERIFICATION:- SUCCESSFUL' in t)!=(mode=='positive') or (mode=='negative' and 'Failed Checks:' not in t):raise SystemExit('STOP own campaign requires inspection')
