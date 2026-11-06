from pathlib import Path
import subprocess,sys,json,hashlib
E=Path(__file__).resolve().parent
for a,m,needs in json.loads((E/sys.argv[1]).read_text()):
 if any(not (E/(dep+'.pass')).exists() or json.loads((E/(dep+'.pass')).read_text())['sha256']!=hashlib.sha256((E/(dep+'.lean')).read_bytes()).hexdigest() for dep in needs):print(a+' skipped missing focused prerequisite',flush=True);continue
 subprocess.run([sys.executable,str(E/'NKR_make.py'),a,m],check=True)
 r=subprocess.run([sys.executable,str(E/'NKR_run.py'),a]);
 if r.returncode==0:(E/(m+'.pass')).write_text(json.dumps(dict(attempt=a,sha256=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest())))
