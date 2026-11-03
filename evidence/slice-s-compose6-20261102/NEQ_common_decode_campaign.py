from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in [(102,'positive'),(103,'wrong_argument'),(104,'wrong_reply'),(105,'wrong_value')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_common_decode.py'),mode],check=True)
 (E/(a+'-common-decode.json')).write_bytes((E/'NEQ_COMMON_DECODE_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::payment_relation::NEQ_common_decode::common_decode'],capture_output=True,text=True);print(a,mode,r.stdout[-1200:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
