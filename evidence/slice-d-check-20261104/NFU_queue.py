"""Serial per-attempt admission; inspect each verdict before dependent work."""
from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent
for item in json.loads((E/sys.argv[1]).read_text()):
 env=dict(os.environ)
 for k,v in item.get('env',{}).items():env[k]=v
 a=item['attempt'];r=subprocess.run([sys.executable,str(E/'NFU_run.py'),a,item['kind'],item['target']],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('No receipt: '+r.stdout+r.stderr)
 rc=json.loads(p.read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if rc['exit_status']!=item['exit']:raise SystemExit('Unexpected verdict; inspect '+a)
