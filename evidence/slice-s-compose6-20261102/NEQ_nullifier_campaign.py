from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,case,mode in [(83,'statement','positive'),(84,'statement','negative'),(85,'payment','positive'),(86,'payment','negative')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_nullifier.py'),case,mode],check=True)
 (E/(a+'-nullifier.json')).write_bytes((E/'NEQ_NULLIFIER_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_nullifier::nullifier_getter'],capture_output=True,text=True);print(a,case,mode,r.stdout[-1100:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
