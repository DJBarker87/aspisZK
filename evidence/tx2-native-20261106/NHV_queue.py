"""Serial owned work queue, never repeats a submitted attempt."""
from pathlib import Path
import json,subprocess,os,sys
E=Path(__file__).resolve().parent
plan=json.loads((E/sys.argv[1]).read_text())
for row in plan:
 a=row['attempt'];kind=row.get('kind','kani');target=row['target']
 if (E/a).exists():raise RuntimeError('Already submitted '+a)
 if row.get('requires'):
  req=E/row['requires']/'receipt.json'
  if not req.exists() or json.loads(req.read_text())['exit_status']!=0:
   print('SKIP dependent',a,flush=True);continue
 env=dict(os.environ)
 if row.get('control'):env['NHV_INVERT']='1'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NHV_run.py'),a,kind,target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(json.dumps(dict(attempt=a,role=row.get('role'),exit=r.returncode)),flush=True)
 if not (E/a/'receipt.json').exists():raise RuntimeError('STOP missing launch receipt '+a)
 if row.get('expected',0)!=r.returncode:
  with (E/'NHV_QUEUE_FINDINGS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected=row.get('expected',0),actual=r.returncode))+'\n')
