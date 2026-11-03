from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in [(106,'positive'),(107,'negative')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_unwrap_borrow.py'),mode],check=True)
 (E/(a+'-unwrap-borrow.json')).write_bytes((E/'NEQ_UNWRAP_BORROW_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','atomic_statement::NEQ_unwrap::unwrap_payload'],capture_output=True,text=True);print(a,mode,r.stdout[-1000:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
