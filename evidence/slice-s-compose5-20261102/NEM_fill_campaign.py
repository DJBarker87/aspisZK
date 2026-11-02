from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,case,mode in [(36,'live','negative'),(37,'late','positive'),(38,'late','negative')]:
 a=f'NEM_K{n:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_fill.py'),case,mode],check=True);(E/(a+'-fill.json')).write_bytes((E/'NEM_FILL_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::pair_tree_profile::NEM_fill::fill_intrinsic'],capture_output=True,text=True);print(a,r.stdout,r.stderr,flush=True)
 assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive') and ('Failed Checks:' in t)==(mode=='negative')
