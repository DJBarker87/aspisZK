from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
plan=[(109,'transfer','positive'),(110,'transfer','wrong_argument'),(111,'transfer','wrong_reply'),(112,'transfer','wrong_value'),(113,'withdrawal','positive'),(114,'withdrawal','wrong_argument'),(115,'withdrawal','wrong_reply'),(116,'withdrawal','wrong_value')]
for n,case,mode in plan:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_payment_decode.py'),case,mode],check=True)
 (E/(a+'-payment-decode.json')).write_bytes((E/'NEQ_PAYMENT_DECODE_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::payment_relation::NEQ_payment_decode::payment_decode'],capture_output=True,text=True);print(a,case,mode,r.stdout[-1200:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
