"""Serial focused continuation; never retry a timed-out shape."""
from pathlib import Path
import json,os,subprocess,time
E=Path(__file__).resolve().parent
env=os.environ.copy();env.update(NGH_CORE='1',NGH_INPUT_SET=str(E/'NGH_OUTER_INPUTS.json'),NGH_PIN_SET=str(E/'NGH_OUTER_PINS.json'))
def receipt(a):return json.loads((E/a/'receipt.json').read_text())
def run(n,target,invert=False,kind='kani'):
 a=f'NGH_{"K"if kind=="kani"else"L"}{n:03}'
 assert not (E/a/'receipt.json').exists()
 e=env.copy()
 if invert:e['NGH_INVERT']='1'
 with (E/(a+'-client.log')).open('w')as f:
  subprocess.run(['python3',str(E/'NGH_run.py'),a,kind,target],env=e,stdout=f,stderr=subprocess.STDOUT)
 assert (E/a/'receipt.json').exists(),'Own runner or transport failure: recover, never resubmit'
 r=receipt(a);print(json.dumps({k:r[k]for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 return r
while not (E/'NGH_K053/receipt.json').exists():time.sleep(3)
n=54
if receipt('NGH_K053')['exit_status']==0:
 run(n,'field::NGH_outer::contract2',True);n+=1
for arity in [3,4]:
 r=run(n,f'field::NGH_outer::contract{arity}');n+=1
 if r['exit_status']==0:
  run(n,f'field::NGH_outer::contract{arity}',True);n+=1
for target in ['copy_positive','copy_negative']:
 if n<=60:run(n,'field::NGH_outer::'+target);n+=1
(E/'NGH_RESUME_QUEUE_RESULT.json').write_text(json.dumps(dict(next_kani=n,completed=True),indent=1)+'\n')
run(22,'NGH_OuterRef',kind='lean')
