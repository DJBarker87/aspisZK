from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
for i,case in enumerate(['transfer_recipient','transfer_change','withdrawal_amount','withdrawal_destination','withdrawal_change']):
 for j,mode in enumerate(['positive','negative']):
  a=f'NEM_K{16+2*i+j:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_payment_call.py'),case,mode],check=True);(E/(a+'-payment-call.json')).write_bytes((E/'NEM_PAYMENT_CALL_CURRENT.json').read_bytes())
  r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::payment_relation::NEM_payment_call::payment_call'],capture_output=True,text=True);print(a,r.stdout,r.stderr,flush=True)
  assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive') and ('Failed Checks:' in t)==(mode=='negative')
