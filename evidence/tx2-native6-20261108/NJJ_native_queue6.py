from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for start,name in [(40, 'query_word'), (42, 'state_roots'), (44, 'gamma_alpha'), (46, 'rho'), (48, 'semantic_slot'), (50, 'z_slot'), (52, 'claim_rhs'), (54, 'power'), (56, 'weight_slot')]:
 for number,control in [(start,False),(start+1,True)]:
  env=os.environ.copy()
  if control:env['NJJ_INVERT']='1'
  a=f'NJJ_K{number:03d}'
  r=subprocess.run(['python3',str(E/'NJJ_run.py'),a,'kani','verifier::NJJ_parent::'+name],env=env)
  if (r.returncode==0)!= (not control):raise RuntimeError((a,r.returncode))
  log=(E/a/'stdout.log').read_text()
  assert 'timed out' not in log
  if control:assert 'VERIFICATION:- FAILED' in log,(a,'no failing verdict')
