"""Final independent members, serial and budget bounded; no promotion from a prefix."""
from pathlib import Path
import os,sys,subprocess,json
E=Path(__file__).resolve().parent;num=int(sys.argv[1])
plans=[
 ('pool_v1::pair_forest_terminal::NEC_result_encode::encode_contract',dict(NEC_RESULT_ENCODE='1')),
 ('r1_pool_adapter::NEC_ctor::withdrawal_contract',dict(NEC_PROGRAM='1',NEC_CTOR='1',NEC_CTOR_CUT='1',NEC_CTOR_FIELD='0')),
 ('pool_v1::pair_forest_terminal::NEC_binding::binding_contract',dict(NEC_BINDING='1',NEC_BINDING_ERROR='first')),
 ('pool_v1::pair_forest_terminal::NEC_binding::binding_contract',dict(NEC_BINDING='1',NEC_BINDING_ERROR='second')),
 ('pool_v1::pair_tree_profile::NEC_decode::live_box',dict(NEC_BRANCH='error')),
 ('r1_pool_adapter::NEC_emit::emit_contract',dict(NEC_PROGRAM='1',NEC_EMIT='1',NEC_EMIT_CUT='1'))]
for target,settings in plans:
 for negative in [False,True]:
  count=sum(json.loads(l)['kind']=='kani' for l in (E/'NEC_ATTEMPTS.jsonl').read_text().splitlines())
  if count>=80:print('Kani budget exhausted; continue pending Lean work',flush=True);raise SystemExit(0)
  env={k:v for k,v in os.environ.items() if not k.startswith('NEC_')};env.update(settings)
  if negative:env['NEC_INVERT']='1'
  a=f'NEC_K{num:03d}';num+=1
  r=subprocess.run([sys.executable,str(E/'NEC_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
  if r.returncode:print(r.stdout[-1500:]+r.stderr[-1500:],flush=True);raise SystemExit(r.returncode)
  receipt=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
  summary=dict(attempt=a,target=target,settings=settings,negative=negative,exit_status=receipt['exit_status'],timeout='CBMC timed out' in log)
  with (E/'NEC_TAIL.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
  print(json.dumps(summary),flush=True)
  if 'error[E' in log or 'error: could not compile' in log:print('Own compiler input requires repair before continuing',flush=True);raise SystemExit(1)
  if not negative and 'VERIFICATION:- SUCCESSFUL' not in log:print('No credit/control; move to next independent member',flush=True);break
  if negative and ('Failed Checks:' not in log or 'CBMC timed out' in log):print('Control not admitted; positive is not paired credit',flush=True)
print('next attempt',num,flush=True)
