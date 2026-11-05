from pathlib import Path
import json,subprocess,sys,os
E=Path(__file__).resolve().parent
for row in json.loads((E/sys.argv[1]).read_text()):
 env=dict(os.environ,NGL_PROGRAM='1');env.update(row.get('env',{}))
 r=subprocess.run([sys.executable,str(E/'NGL_run.py'),row['attempt'],row['kind'],row['target']],env=env,capture_output=True,text=True)
 print(row['attempt'],r.returncode,r.stdout[-800:],r.stderr[-500:],flush=True)
 p=E/row['attempt']/'receipt.json'
 if not p.exists():raise SystemExit('No receipt; stop and recover without resubmission')
 x=json.loads(p.read_text());o=(E/row['attempt']/'stdout.log').read_text()
 with (E/'NGL_QUEUE_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(row,client_exit=r.returncode,exit=x['exit_status'],matched=(x['exit_status']==row['expected'])))+'\n')
 if x['exit_status']!=row['expected']:raise SystemExit('Unexpected result; isolate before proceeding')
 if row['expected'] and ('VERIFICATION:- FAILED' not in o or not any(tag in o.lower() for tag in ['assertion','postcondition','ensures','failed checks: |r|'])):raise SystemExit('Control is not an assertion failure')
