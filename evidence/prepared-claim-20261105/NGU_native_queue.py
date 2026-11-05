from pathlib import Path
import sys,subprocess,json,os
E=Path(__file__).resolve().parent
pairs=[]
for target in sys.argv[1:]:
 row=dict(harness=target)
 for control in [False,True]:
  records=[json.loads(l) for l in (E/'NGU_ATTEMPTS.jsonl').read_text().splitlines()]
  n=max([int(x['attempt'][-3:]) for x in records if x['attempt'].startswith('NGU_K')]+[0])+1
  assert n<=40,'Kani budget exhausted'
  a=f'NGU_K{n:03}';env=dict(os.environ)
  if control:env['NGU_INVERT']='1'
  else:env.pop('NGU_INVERT',None)
  r=subprocess.run([sys.executable,str(E/'NGU_run.py'),a,'kani','verifier::NGU_stages::'+target],env=env)
  rc=json.loads((E/a/'receipt.json').read_text());raw=(E/a/'stdout.log').read_text()
  status='MATCHED_CONTROL_FAIL' if control and r.returncode==1 and 'VERIFICATION:- FAILED' in raw and (('assertion failed: actual == expected ^ XOR' in raw) or (' ** 1 of ' in raw and 'core::panicking::assert_failed_inner' in raw)) else 'PASS' if not control and r.returncode==0 and 'VERIFICATION:- SUCCESSFUL' in raw else 'EXCLUDED'
  row['control' if control else 'positive']=dict(attempt=a,status=status,exit=rc['exit_status'])
  with (E/'NGU_NATIVE_QUEUE.jsonl').open('a') as f:f.write(json.dumps(dict(harness=target,control=control,attempt=a,status=status))+'\n')
  if status=='EXCLUDED':print(json.dumps(row));sys.exit(1)
 pairs.append(row);print(json.dumps(row),flush=True)
with (E/'NGU_NATIVE_PAIRS.jsonl').open('a') as f:
 for r in pairs:f.write(json.dumps(r)+'\n')
