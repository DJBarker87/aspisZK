from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in [(42,'positive'),(43,'negative')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_root_geometry.py'),mode],check=True)
 (E/(a+'-geometry.json')).write_bytes((E/'NEQ_ROOT_GEOMETRY_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_root_prefix::root_geometry'],capture_output=True,text=True);print(a,mode,r.stdout[-1000:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
