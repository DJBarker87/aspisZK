from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
plan=[(87,'header','positive'),(88,'header','value'),(89,'header','guard'),(90,'m31','positive'),(91,'m31','value'),(92,'m31','guard'),(93,'digest','positive'),(94,'digest','value'),(95,'digest','guard')]
for n,case,mode in plan:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_decode_scalar.py'),case,mode],check=True)
 (E/(a+'-decode-scalar.json')).write_bytes((E/'NEQ_DECODE_SCALAR_CURRENT.json').read_bytes())
 harness=('pool_v1::payment_relation' if case=='header' else 'atomic_statement')+'::NEQ_decode_scalar::decode_scalar'
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani',harness],capture_output=True,text=True);print(a,case,mode,r.stdout[-1100:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
