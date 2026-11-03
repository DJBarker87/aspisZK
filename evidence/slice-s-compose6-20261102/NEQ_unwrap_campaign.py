from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,width,mode in [(96,4,'positive'),(97,4,'negative'),(98,8,'positive'),(99,8,'negative'),(100,32,'positive'),(101,32,'negative')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_unwrap.py'),str(width),mode],check=True)
 (E/(a+'-unwrap.json')).write_bytes((E/'NEQ_UNWRAP_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','atomic_statement::NEQ_unwrap::unwrap_payload'],capture_output=True,text=True);print(a,width,mode,r.stdout[-1000:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
