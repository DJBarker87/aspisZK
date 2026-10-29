"""Lane-owned serial window plan; never run a control after an unproved positive."""
from pathlib import Path
import os,subprocess,json,sys
E=Path(__file__).resolve().parent
num=int(sys.argv[1]);phase=sys.argv[2]
if phase=='afterstate-fields':
 plans=[('pool_v1::pair_tree_profile::NEC_decode::afterstate_box',dict(NEC_PURE_VALUE='1',NEC_RAW_CARRIER='1',NEC_BRANCH='success',NEC_GROUP=str(g))) for g in [1,2]]
elif phase=='static-after':plans=[('pool_v1::pair_tree_profile::NEC_static_decode::after_contract',dict(NEC_STATIC='1',NEC_STATIC_AFTER_BOUND='1',NEC_GROUP=str(g))) for g in [1,2]]
elif phase=='live-error':plans=[('pool_v1::pair_tree_profile::NEC_decode::live_box',dict(NEC_BRANCH='error'))]
elif phase=='derived-binding':plans=[('pool_v1::pair_forest_terminal::NEC_binding::binding_contract',dict(NEC_BINDING='1',NEC_BINDING_DERIVED='1'))]
elif phase=='live-window':plans=[('NEC_live_step::selected_window',dict(NEC_LIVE_STEP='1'))]
else:raise ValueError(phase)
for target,settings in plans:
 for negative in [False,True]:
  env={k:v for k,v in os.environ.items() if not k.startswith('NEC_')};env.update(settings)
  if negative:env['NEC_INVERT']='1'
  a=f'NEC_K{num:03d}';num+=1
  r=subprocess.run([sys.executable,str(E/'NEC_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
  if r.returncode:
   print(r.stdout[-1000:]+r.stderr[-2000:],flush=True);raise SystemExit(r.returncode)
  receipt=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
  summary=dict(attempt=a,phase=phase,settings=settings,negative=negative,exit_status=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'])
  with (E/'NEC_QUEUE.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
  print(json.dumps(summary),flush=True)
  if not negative and 'VERIFICATION:- SUCCESSFUL' not in log:
   print('No credit/control: split or diagnose this positive before returning to it.',a,flush=True);break
  if negative and ('Failed Checks:' not in log or 'timed out' in log.lower()):
   print('Control not admitted; retain positive as fragment.',a,flush=True)
print('next attempt',num,flush=True)
