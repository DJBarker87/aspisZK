from pathlib import Path
import os,subprocess
E=Path(__file__).resolve().parent;number=112
for name in ['weight04','accumulate00','accumulate01','accumulate02']:
 for control in [False,True]:
  a=f'NHM_K{number:03}';number+=1
  r=subprocess.run(['python3',str(E/'NHM_run.py'),a,'kani','weights::NHM_group::'+name],env=dict(os.environ,**({'NHM_INVERT':'1'}if control else{})))
  log=(E/a/'stdout.log').read_text()
  assert ('VERIFICATION:- FAILED'if control else'VERIFICATION:- SUCCESSFUL')in log and'timed out'not in log.lower()and'unwinding failures'not in log,(a,r.returncode)
