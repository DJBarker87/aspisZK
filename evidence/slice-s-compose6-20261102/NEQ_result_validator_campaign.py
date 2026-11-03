from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in [(44,'positive'),(45,'wrong_lane'),(46,'wrong_after'),(47,'wrong_reply')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_result_validator.py'),mode],check=True)
 (E/(a+'-result-validator.json')).write_bytes((E/'NEQ_RESULT_VALIDATOR_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_result_validator::result_validator'],capture_output=True,text=True);print(a,mode,r.stdout[-1400:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
