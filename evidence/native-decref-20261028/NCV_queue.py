"""Serial native subdomain queue; inverse controls run only after a positive pass."""
from pathlib import Path
import subprocess,json,os
E=Path(__file__).resolve().parent
jobs=[(case,name) for case in ['long','empty','version','encoding'] for name in ['master','checkpoint','lane']]+[('lanes','master'),('lanes','checkpoint'),('depth','lane')]
for case,name in jobs:
 for inverse in [False,True]:
  attempts=[json.loads(l) for l in (E/'NCV_ATTEMPTS.jsonl').read_text().splitlines()]
  k=sum(x['kind']=='kani' for x in attempts)+1
  if k>60:raise SystemExit('Kani allocation exhausted')
  a=f'NCV_K{k:03d}';env=dict(os.environ,NCV_CASE=case)
  if inverse:env['NCV_NEGATIVE']='1'
  else:env.pop('NCV_NEGATIVE',None)
  print(a,case,name,'inverse' if inverse else 'positive',flush=True)
  r=subprocess.run(['python3',str(E/'NCV_run.py'),a,'kani','r1_pool_adapter::NCV_native::NCV_'+name+'_contract'],env=env)
  if r.returncode:raise SystemExit(r.returncode)
  rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
  if not inverse and rc['exit_status']!=0:
   print('Positive did not pass; skip its inverse, continue independent member',flush=True);break
  if inverse:
   assert rc['exit_status']!=0 and ' ** 1 of' in log and '!NCV_native::matches_' in log and 'unwinding assertion' not in log, 'inspect negative control before continuing'
