from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
number=17
for name,groups in [('partial',8),('high',6),('byte',8)]:
 for g in range(groups):
  for control in [False,True]:
   a=f'NHM_K{number:03}';number+=1
   env=dict(os.environ)
   if control:env['NHM_INVERT']='1'
   r=subprocess.run(['python3',str(E/'NHM_run.py'),a,'kani',f'weights::NHM_windows::{name}{g:02}'],env=env)
   rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
   assert ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL') in log,(a,r.returncode)
