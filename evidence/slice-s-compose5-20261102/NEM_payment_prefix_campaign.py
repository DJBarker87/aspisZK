from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
for n,case,mode in [(12,'transfer','positive'),(13,'transfer','negative'),(14,'withdrawal','positive'),(15,'withdrawal','negative')]:
 a=f'NEM_K{n:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_payment_prefix.py'),case,mode],check=True);(E/(a+'-payment-prefix.json')).write_bytes((E/'NEM_PAYMENT_PREFIX_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::payment_relation::NEM_payment_prefix::payment_prefix'],capture_output=True,text=True);print(a,r.stdout,r.stderr,flush=True)
 assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive') and ('Failed Checks:' in t)==(mode=='negative')
