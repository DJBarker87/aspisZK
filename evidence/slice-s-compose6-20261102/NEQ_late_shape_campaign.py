from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
plan=[(8,'caller','full_mutation_caller',True),(9,'wrong_window','full_mutation_caller',False),(10,'inside_unimplied','full_mutation_caller',False)]
for n,mode,harness,success in plan:
 a=f'NEQ_K{n:03}'
 subprocess.run([sys.executable,str(E/'NEQ_prepare_late_contract.py'),mode],check=True)
 (E/(a+'-shape.json')).write_bytes((E/'NEQ_SLICE_CONTRACT_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_slice_contract::'+harness],capture_output=True,text=True)
 print(a,mode,r.stdout[-1500:],r.stderr,flush=True)
 log=(E/a/'stdout.log').read_text()
 assert ('VERIFICATION:- SUCCESSFUL' in log)==success
 assert success or ('VERIFICATION:- FAILED' in log and 'Failed Checks:' in log)
 assert 'timed out' not in log.lower()
