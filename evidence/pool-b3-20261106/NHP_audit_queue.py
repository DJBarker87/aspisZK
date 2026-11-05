from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,kind,target in [('NHP_L011','link','NHP_ProofDriver'),('NHP_L012','link','NHP_Driver'),('NHP_L013','audit','fixtures'),('NHP_L014','audit','batch0'),('NHP_L015','audit','scan')]:
 r=subprocess.run([sys.executable,str(E/'NHP_run.py'),a,kind,target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(json.dumps(dict(attempt=a,kind=kind,target=target,exit=r.returncode)),flush=True)
 if r.returncode:sys.exit(r.returncode)
