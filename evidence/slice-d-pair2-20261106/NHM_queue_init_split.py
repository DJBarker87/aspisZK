from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
number=81
for g in [1,2,3,4,5,6,7,8,9]:
 for control in [False,True]:
  a=f'NHM_K{number:03}';number+=1
  env=dict(os.environ,NHM_CORE='1')
  if control:env['NHM_INVERT']='1'
  r=subprocess.run(['python3',str(E/'NHM_run.py'),a,'kani',f'NHM_init::init{g:02}'],env=env)
  log=(E/a/'stdout.log').read_text()
  assert ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL') in log and 'timed out'not in log.lower() and 'unwinding failures'not in log,(a,r.returncode)
