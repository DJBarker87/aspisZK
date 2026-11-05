from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[('lean','NIM_ProofDriver'),('link','NIM_ProofDriver'),('lean','NIM_Driver'),('link','NIM_Driver'),('audit','fixtures'),('audit','scan')]+[('audit','batch'+str(i))for i in range(7)]
for i,(k,t) in enumerate(jobs,28):
 r=subprocess.run([sys.executable,str(E/'NIM_run.py'),f'NIM_L{i:03}',k,t])
 if r.returncode and k!='audit':sys.exit(r.returncode)
