"""Serial adaptive domain partition, same harness name/property; no cap increases."""
from pathlib import Path
import subprocess,json,os,sys
E=Path(__file__).resolve().parent
queue=[(20,30),(35,45),(50,55),(60,65),(70,75),(80,85),(90,95),(100,105)]
next_attempt=10;accepted=[dict(lo=1,hi=16,stride=1,positive='NEV_K008',negative='NEV_K009'),dict(lo=110,hi=110,stride=1,positive='NEV_K006',negative='NEV_K007')];failed=[]
def run(lo,hi,wrong=False):
 global next_attempt
 a=f'NEV_K{next_attempt:03}';next_attempt+=1
 env=dict(os.environ)
 if wrong:env['NEV_RUST_CFG']='NEV_wrong_fixed_offsets'
 r=subprocess.run([sys.executable,str(E/'NEV_run.py'),a,'kani','verifier::NEV_prefix_step::prefix_push_fixed_offsets'],env=env,capture_output=True,text=True)
 (E/(a+'-campaign.log')).write_text(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text())
 log=(E/a/'stdout.log').read_text()
 print(json.dumps(dict(attempt=a,lo=lo,hi=hi,negative=wrong,exit=rc['exit_status'],wall=rc['wall_seconds'],last=log[-300:])),flush=True)
 return a,rc,log
while queue and next_attempt<=58:
 lo,hi=queue.pop(0)
 subprocess.run([sys.executable,str(E/'NEV_prefix_exact.py'),str(lo),str(hi),'5'],check=True)
 a,rc,log=run(lo,hi)
 if rc['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log:
  b,nr,nlog=run(lo,hi,True)
  if nr['exit_status']!=0 and 'VERIFICATION:- FAILED' in nlog and 'timed out' not in nlog and 'CBMC failed' not in nlog:
   accepted.append(dict(lo=lo,hi=hi,stride=5,positive=a,negative=b))
  else:
   failed.append(dict(lo=lo,hi=hi,attempt=b,phase='negative'))
   if lo<hi:
    mid=lo+5*((hi-lo)//10);queue[:0]=[(lo,mid),(mid+5,hi)]
 else:
  failed.append(dict(lo=lo,hi=hi,attempt=a,phase='positive'))
  if 'timed out' in log or rc['exit_status'] in [124,137]:
   if lo<hi:
    mid=lo+5*((hi-lo)//10);queue[:0]=[(lo,mid),(mid+5,hi)]
  else:raise RuntimeError('Unexpected positive failure: inspect, do not continue')
 (E/'NEV_PREFIX_CAMPAIGN.json').write_text(json.dumps(dict(accepted=accepted,failed=failed,pending=queue,next_attempt=next_attempt),indent=2)+'\n')
print('campaign terminal',next_attempt,queue,flush=True)
