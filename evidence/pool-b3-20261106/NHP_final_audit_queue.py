from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,kind,target in [('NHP_L022','audit','batch1'),('NHP_L023','audit','scan')]:
 r=subprocess.run([sys.executable,str(E/'NHP_run.py'),a,kind,target],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(json.dumps(dict(attempt=a,target=target,exit=r.returncode)),flush=True)
 if r.returncode:sys.exit(r.returncode)
