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
 if row.get('append_combined'):
  p=E/'NHV_COMBINED_IMPORT.lean';p.write_text(p.read_text()+row['append_combined'])
 env=dict(os.environ)
 if row.get('control'):env['NHV_INVERT']='1'
 if 'corrupt_argument' in row:env['NHV_CORRUPT_ARGUMENT']=str(row['corrupt_argument'])
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NHV_run.py'),a,kind,target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(json.dumps(dict(attempt=a,role=row.get('role'),exit=r.returncode)),flush=True)
 if not (E/a/'receipt.json').exists():raise RuntimeError('STOP missing launch receipt '+a)
 if row.get('stop_on_error') and row.get('expected',0)!=r.returncode:raise RuntimeError('Focused target failed; repair before dependencies: '+a)
 if row.get('expected',0)!=r.returncode:
  with (E/'NHV_QUEUE_FINDINGS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected=row.get('expected',0),actual=r.returncode))+'\n')
