"""Own serial proof queue. A timeout/kill stops for inspection, never replayed."""
from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
q=json.loads(Path(sys.argv[1]).read_text())
for x in q:
 a=x['attempt']; env=dict(os.environ)
 if x.get('control'):env['NID_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NID_run.py'),a,x.get('kind','kani'),x['target']],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout)
 p=E/a/'receipt.json'
 if not p.exists():print(r.stdout[-2000:]);sys.exit(r.returncode or 1)
 rc=json.loads(p.read_text());out=(E/a/'stdout.log').read_text()
 good=rc['exit_status']==0 if not x.get('control') else rc['exit_status']!=0 and 'VERIFICATION:- FAILED' in out and 'assertion' in out.lower()
 print(json.dumps(dict(attempt=a,expected_control=x.get('control',False),exit=rc['exit_status'],matched=good)),flush=True)
 if not good:print(r.stdout[-2000:]);sys.exit(1)
