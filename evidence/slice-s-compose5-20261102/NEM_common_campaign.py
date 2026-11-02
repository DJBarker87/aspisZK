from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
for a,case,mode in [(6,'anchor','positive'),(7,'anchor','negative'),(8,'nullifier','positive'),(9,'nullifier','negative'),(10,'asset','positive'),(11,'asset','negative')]:
 n=f'NEM_K{a:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_common_call.py'),case,mode],check=True)
 (E/(n+'-common-call.json')).write_bytes((E/'NEM_COMMON_CALL_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),n,'kani','pool_v1::payment_relation::NEM_common_call::common_call'],capture_output=True,text=True)
 print(n,r.stdout,r.stderr,flush=True)
 assert (E/n/'receipt.json').exists(),'unresolved launch: do not resubmit'
 log=(E/n/'stdout.log').read_text();assert 'timed out' not in log.lower(),'split before further work'
 assert ('VERIFICATION:- SUCCESSFUL' in log)==(mode=='positive') and ('Failed Checks:' in log)==(mode=='negative')
