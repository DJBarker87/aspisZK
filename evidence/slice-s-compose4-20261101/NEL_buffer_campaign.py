from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
cases=['late_fill','late_after_copy','payment_transfer_recipient','payment_transfer_change','payment_withdraw_amount','payment_withdraw_destination','payment_withdraw_change']
n=14
for case in cases:
 for mode in ['positive','negative']:
  a=f'NEL_K{n:03}';n+=1
  subprocess.run([sys.executable,str(E/'NEL_prepare_buffer_step.py'),case,mode],check=True)
  (E/(a+'-window.json')).write_bytes((E/'NEL_BUFFER_CURRENT.json').read_bytes())
  file='pair_tree_profile' if case.startswith('late') else 'payment_relation'
  r=subprocess.run([sys.executable,str(E/'NEL_kani_run.py'),a,'kani',f'pool_v1::{file}::NEL_buffer_step::buffer_step'],text=True,capture_output=True)
  print(a,case,mode,r.stdout[-1100:],r.stderr,flush=True)
  if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved submission or own input error')
  log=(E/a/'stdout.log').read_text();rc=json.loads((E/a/'receipt.json').read_text())
  if 'timed out' in log.lower() or rc['exit_status'] in [124,137]:
   print('TIMEOUT/KILL: this shape cannot rerun unchanged; skip matching control and continue independent case',flush=True)
   n+=(mode=='positive');break
  if ('VERIFICATION:- SUCCESSFUL' in log)!=(mode=='positive') or (mode=='negative' and 'Failed Checks:' not in log):raise SystemExit('STOP inspect own inputs or counterexample')
