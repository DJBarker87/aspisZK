from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
for n,case,mode in [(30,'live','positive'),(31,'live','negative'),(32,'after','positive'),(33,'after','negative')]:
 a=f'NEM_K{n:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_validator_prefix.py'),case,mode],check=True);(E/(a+'-validator-prefix.json')).write_bytes((E/'NEM_VALIDATOR_PREFIX_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::'+('pair_tree_profile' if case=='live' else 'pair_terminal')+'::NEM_validator_prefix::validator_prefix'],capture_output=True,text=True);print(a,r.stdout,r.stderr,flush=True)
 assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive') and ('Failed Checks:' in t)==(mode=='negative')
