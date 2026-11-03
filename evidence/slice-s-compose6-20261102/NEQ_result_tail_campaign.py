from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in [(76,'positive'),(77,'wrong_after'),(78,'wrong_byte'),(79,'wrong_reply')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_result_tail.py'),mode],check=True)
 (E/(a+'-result-tail.json')).write_bytes((E/'NEQ_RESULT_TAIL_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_result_window::result_tail'],capture_output=True,text=True);print(a,mode,r.stdout[-1100:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
