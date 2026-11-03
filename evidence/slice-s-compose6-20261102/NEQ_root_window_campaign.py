from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
plan=[(15+2*i+k,i,mode) for i in range(10) for k,mode in enumerate(['positive','negative'])]+[(35,9,'wrong_place')]
for n,slot,mode in plan:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_root_window.py'),str(slot),mode],check=True)
 (E/(a+'-window.json')).write_bytes((E/'NEQ_ROOT_WINDOW_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_root_window::root_window'],capture_output=True,text=True);print(a,slot,mode,r.stdout[-1400:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
