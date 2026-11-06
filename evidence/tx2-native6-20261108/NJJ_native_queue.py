from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for start,name in [(11,'weight_iterator'),(13,'map_allocation64'),(15,'pending_step'),(17,'flush_step')]:
 for number,control in [(start,False),(start+1,True)]:
  env=os.environ.copy()
  if control:env['NJJ_INVERT']='1'
  a=f'NJJ_K{number:03d}'
  r=subprocess.run(['python3',str(E/'NJJ_run.py'),a,'kani','verifier::NJJ_parent::'+name],env=env)
  if (r.returncode==0)!= (not control):raise RuntimeError((a,r.returncode))
  receipt=json.loads((E/a/'receipt.json').read_text());assert receipt['exit_status']!=124
  log=(E/a/'stdout.log').read_text()
  if control:assert 'VERIFICATION:- FAILED' in log or 'VERIFICATION FAILED' in log or 'Status: FAILURE' in log,(a,'no failing verdict')
