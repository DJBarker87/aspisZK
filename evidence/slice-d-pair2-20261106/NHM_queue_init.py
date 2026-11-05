from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for g in range(1,4):
 for control in [False,True]:
  a=f'NHM_K{80+2*(g-1)+int(control):03}'
  env=dict(os.environ,NHM_CORE='1')
  if control:env['NHM_INVERT']='1'
  r=subprocess.run(['python3',str(E/'NHM_run.py'),a,'kani',f'NHM_init::init{g:02}'],env=env)
  rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
  assert ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL') in log,(a,r.returncode)
