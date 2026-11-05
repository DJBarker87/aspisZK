from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for fam,base in [('dispatch',44),('partial',52)]:
 for g in range(4):
  for control in [False,True]:
   n=base+g*2+int(control);env=dict(os.environ)
   if control:env.update(NHX_INVERT='1',NHX_NATIVE_CFG='NHX_corrupt')
   subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_K{n:03}','kani',f'weights::NHX_parents::{fam}{g:02}'],env=env)
   log=(E/f'NHX_K{n:03}/stdout.log').read_text()
   if ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL')not in log or 'timed out'in log.lower()or'unwinding failures'in log:raise SystemExit(f'nonqualifying {n}')
