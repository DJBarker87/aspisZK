from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for start,name in [(16,'pending_window'),(18,'flush_step'),(20,'pending_start'),(22,'pending_end'),(24,'value')]:
 for number,control in [(start,False),(start+1,True)]:
  env=os.environ.copy()
  if control:env['NJJ_INVERT']='1'
  a=f'NJJ_K{number:03d}'
  r=subprocess.run(['python3',str(E/'NJJ_run.py'),a,'kani','verifier::NJJ_parent::'+name],env=env)
  if (r.returncode==0)!= (not control):raise RuntimeError((a,r.returncode))
  log=(E/a/'stdout.log').read_text()
  assert 'timed out' not in log
  if control:assert 'VERIFICATION:- FAILED' in log,(a,'no failing verdict')
