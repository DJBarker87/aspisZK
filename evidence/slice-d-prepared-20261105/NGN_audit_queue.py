from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(27,'lean','NGN_COMBINED_IMPORT'),(28,'link','NGN_ProofDriver'),(29,'link','NGN_Driver'),(30,'audit','fixtures'),(31,'audit','batch0'),(32,'audit','scan')]
for n,k,t in jobs:
 a=f'NGN_L{n:03d}';r=subprocess.run([sys.executable,str(E/'NGN_run.py'),a,k,t],text=True,capture_output=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,r.returncode,r.stdout[-1500:],flush=True)
 if r.returncode:break
