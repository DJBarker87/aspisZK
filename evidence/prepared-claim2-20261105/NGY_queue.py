"""Own serial plan client, no parallel scopes and no automatic proof retries."""
from pathlib import Path
import subprocess,json,sys,os
E=Path(__file__).resolve().parent
plan=json.loads(Path(sys.argv[1]).read_text())
for row in plan:
 env=os.environ.copy()
 if row.get('corrupt'):env['NGY_CORRUPT']='1'
 if row.get('range'):env['NGY_RANGE']=row['range']
 if 'tile' in row:env['NGY_TILE']=str(row['tile'])
 if row.get('field_corrupt'):env['NGY_FIELD_CORRUPT']='1'
 if row.get('weak_false'):env['NGY_WEAK_FALSE']='1'
 r=subprocess.run([sys.executable,str(E/'NGY_run.py'),row['attempt'],row['kind'],row['target']],env=env)
 receipt=E/row['attempt']/'receipt.json'
 if not receipt.exists():raise SystemExit('Missing receipt; do not relaunch')
 x=json.loads(receipt.read_text());log=(E/row['attempt']/'stdout.log').read_text()
 ok=x['exit_status']==0 if row.get('expect','pass')=='pass' else (x['exit_status']!=0 and 'Failed Checks:' in log and row.get('needle','f_ref') in log and 'timed out' not in log)
 with (E/'NGY_QUEUE.jsonl').open('a') as f:f.write(json.dumps(dict(**row,client_exit=r.returncode,expected_outcome=ok))+'\n')
 if not ok:raise SystemExit('Review failed/unexpected attempt; no dependent launch')
