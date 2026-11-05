from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,kind,target in [(29,'lean','NHC_ProofDriver'),(30,'lean','NHC_Driver'),(31,'link','NHC_ProofDriver'),(32,'link','NHC_Driver'),(33,'audit','fixtures'),(34,'audit','batch0'),(35,'audit','scan')]:
 a=f'NHC_L{i:03}';r=subprocess.run([sys.executable,str(E/'NHC_run.py'),a,kind,target],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,kind,target,r.returncode,flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-2200:]);sys.exit(r.returncode)
