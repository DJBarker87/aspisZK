from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1])
for shape in ['header','send']:
 for mode in ['positive','negative']:
  a=f'NEU_K{n:03}';n+=1
  subprocess.run([sys.executable,str(E/'NEU_prepare_emit_cut.py'),shape,mode],check=True)
  (E/(a+'-emit-cut.json')).write_bytes((E/'NEU_EMIT_CUT_CURRENT.json').read_bytes())
  r=subprocess.run([sys.executable,str(E/'NEU_program_kani_run.py'),a,'kani','r1_pool_adapter::NEU_emit_cut::emission_cut'],capture_output=True,text=True)
  print(a,shape,mode,r.stdout[-1100:],r.stderr,flush=True)
  t=(E/a/'stdout.log').read_text()
  if 'timed out' in t.lower():print('excluded timeout; next independent cut',flush=True);break
  if ('VERIFICATION:- SUCCESSFUL' in t)!=(mode=='positive') or (mode=='negative' and 'Failed Checks:' not in t):raise SystemExit('STOP own campaign requires inspection')
