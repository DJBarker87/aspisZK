from pathlib import Path
import subprocess,json,os
E=Path(__file__).resolve().parent
items=['identity_body','policy_body','word32','word64','sequence_frame','sequence_capacity','frontier_guard','empty_guard','key_zero','magic_equal','asset_canonical','policy_flags','master_chronology','lane_id','binding_entry','empty_entry']
def count():return sum(json.loads(l)['kind']=='kani' for l in (E/'NCV_ATTEMPTS.jsonl').read_text().splitlines())
def run(target,inverse=False):
 k=count()+1;assert k<=60
 a=f'NCV_K{k:03d}';env=dict(os.environ);env.pop('NCV_CASE',None)
 if inverse:env['NCV_NEGATIVE']='1'
 else:env.pop('NCV_NEGATIVE',None)
 print(a,target,'inverse' if inverse else 'positive',flush=True)
 r=subprocess.run(['python3',str(E/'NCV_run.py'),a,'kani',target],env=env)
 if r.returncode:raise SystemExit(r.returncode)
 return json.loads((E/a/'receipt.json').read_text()),(E/a/'stdout.log').read_text()
for name in items:
 if count()>58:break # preserve a matched negative slot for every positive
 target='r1_pool_adapter::NCV_native::NCV_fragments::NCV_'+name+'_step'
 rc,log=run(target)
 if 'Failed to match the following harness' in log:raise SystemExit('Own target error: stop queue before another launch')
 if rc['exit_status']!=0:
  print('No credit; inverse skipped; continue independent fragment',flush=True);continue
 rc,log=run(target,True)
 if not (rc['exit_status']!=0 and ' ** 1 of' in log and 'Failed Checks:' in log):
  raise SystemExit('Unexpected negative control; inspect before continuing')
for name in ['copy','frame']:
 if count()>=60:break
 target='r1_pool_adapter::NCV_native::NCV_box::NCV_box_'+name+'_check'
 rc,log=run(target)
 if rc['exit_status']==0 and count()<60:
  rc,log=run(target,True)
  if not (rc['exit_status']!=0 and 'Failed Checks:' in log):raise SystemExit('Unexpected Box control')
print('Fragment/Box sequence terminal; runs',count(),flush=True)
