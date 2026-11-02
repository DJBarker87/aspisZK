from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
for n,case,mode in [(26,'live','positive'),(27,'live','negative'),(28,'after','positive'),(29,'after','negative')]:
 a=f'NEM_K{n:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_frontier_validator.py'),case,mode],check=True);(E/(a+'-frontier-validator.json')).write_bytes((E/'NEM_FRONTIER_VALIDATOR_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::'+('pair_tree_profile' if case=='live' else 'pair_terminal')+'::NEM_frontier_validator::frontier_validator'],capture_output=True,text=True);print(a,r.stdout,r.stderr,flush=True)
 assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive') and ('Failed Checks:' in t)==(mode=='negative')
