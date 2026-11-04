"""Own sequential validation driver; never alters the shared launcher."""
from pathlib import Path
import subprocess,json,os,sys
E=Path(__file__).resolve().parent
queue=json.loads((E/sys.argv[1]).read_text())
for item in queue:
 env=dict(os.environ,**item.get('env',{}));attempt=item['attempt']
 r=subprocess.run([sys.executable,str(E/'NGD_run.py'),attempt,item['kind'],item['target']],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(attempt+'-client.log')).write_text(r.stdout)
 print(json.dumps(dict(attempt=attempt,exit=r.returncode,expected=item['exit'])),flush=True)
 if r.returncode!=item['exit']:raise SystemExit('Review required; no dependent launch: '+attempt+' '+r.stdout[-1000:])
