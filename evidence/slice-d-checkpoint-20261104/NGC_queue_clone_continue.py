from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
# K066 was an optional std-implementation stress shape and timed out. Its
# unchanged controls/other resize variants are not launched. Clone is independent.
for k,typ in [(74,'u8'),(76,'q'),(78,'raw'),(80,'wide')]:
 for invert in [False,True]:
  a=f'NGC_K{k+int(invert):03}';env=dict(os.environ)
  if invert:env['NGC_INVERT']='1'
  with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'kani','verifier::NGC_windows::clone_value_'+typ],env=env,stdout=f,stderr=subprocess.STDOUT)
  print(a,r.returncode,flush=True)
  if r.returncode!=(1 if invert else 0):raise RuntimeError(a)
