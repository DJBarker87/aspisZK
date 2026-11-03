from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,case,mode in [(118,'borrow_length','positive'),(119,'borrow_length','negative'),(120,'request_prefix','positive')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_final_native.py'),case,mode],check=True)
 (E/(a+'-final-native.json')).write_bytes((E/'NEQ_FINAL_NATIVE_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_final_native::final_native'],capture_output=True,text=True);print(a,case,mode,r.stdout[-1100:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
