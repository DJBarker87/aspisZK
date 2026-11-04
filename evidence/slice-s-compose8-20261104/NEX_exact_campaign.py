from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1])
for width in [8,32]:
 for mode in ['positive','negative']:
  a=f'NEX_K{n:03}';n+=1;assert n<=141
  subprocess.run([sys.executable,str(E/'NEX_prepare_exact.py'),str(width),mode],check=True)
  (E/(a+'-shape.json')).write_bytes((E/'NEX_EXACT_CURRENT.json').read_bytes())
  r=subprocess.run([sys.executable,str(E/'NEX_kani_run.py'),a,'kani','pool_v1::pair_terminal::NEX_exact::exact_cut'],capture_output=True,text=True)
  print(a,width,mode,r.stdout[-1000:],r.stderr,flush=True)
  log=(E/a/'stdout.log').read_text()
  if ('VERIFICATION:- SUCCESSFUL' in log)!=(mode=='positive') or (mode=='negative' and 'Failed Checks:' not in log):raise SystemExit('excluded or unexpected verdict; inspect, never rerun unchanged')
