from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for g in range(4):
 for control in [False,True]:
  n=24+g*2+int(control);env=dict(os.environ)
  if control:env.update(NHX_INVERT='1',NHX_NATIVE_CFG='NHX_corrupt')
  subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_K{n:03}','kani',f'weights::NHX_parents::dispatch{g:02}'],env=env)
  log=(E/f'NHX_K{n:03}/stdout.log').read_text()
  if ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL')not in log or 'timed out'in log.lower()or'unwinding failures'in log:raise SystemExit(f'nonqualifying {n}')
for n,target in [(32,'KMX_ptr_wrong'),(33,'KMX_slice_wrong')]:
 subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_K{n:03}','kani','weights::NHX_parents::KMX_checks::'+target])
 log=(E/f'NHX_K{n:03}/stdout.log').read_text()
 assert 'VERIFICATION:- FAILED'in log and 'timed out'not in log.lower()and'unwinding failures'not in log
