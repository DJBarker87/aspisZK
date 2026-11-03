from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;n=int(sys.argv[1]);start=int(sys.argv[2]);end=int(sys.argv[3]);branch=sys.argv[4]
for slot in range(start,end):
 for mode in ['positive','negative']:
  assert n<=130
  a=f'NEU_K{n:03}';n+=1
  subprocess.run([sys.executable,str(E/'NEU_prepare_box.py'),branch,str(slot),mode],check=True)
  (E/(a+'-box.json')).write_bytes((E/'NEU_BOX_CURRENT.json').read_bytes())
  r=subprocess.run([sys.executable,str(E/'NEU_program_kani_run.py'),a,'kani','r1_pool_adapter::NEU_box::box_window'],capture_output=True,text=True)
  print(a,branch,slot,mode,r.stdout[-1000:],r.stderr,flush=True)
  t=(E/a/'stdout.log').read_text()
  if 'timed out' in t.lower():print('EXCLUDED timeout; no unchanged retry; inspect before next slot',flush=True);raise SystemExit(2)
  if ('VERIFICATION:- SUCCESSFUL' in t)!=(mode=='positive') or (mode=='negative' and 'Failed Checks:' not in t):raise SystemExit('STOP own campaign requires source/error inspection')
