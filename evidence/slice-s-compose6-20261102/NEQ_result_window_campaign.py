from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
plan=[(48+2*i+k,i,mode) for i in range(9) for k,mode in enumerate(['positive','negative'])]+[(66,7,'wrong_place'),(67,8,'wrong_place')]
for n,slot,mode in plan:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_result_window.py'),str(slot),mode],check=True)
 (E/(a+'-result-window.json')).write_bytes((E/'NEQ_RESULT_WINDOW_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_result_window::result_window'],capture_output=True,text=True);print(a,slot,mode,r.stdout[-1100:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
