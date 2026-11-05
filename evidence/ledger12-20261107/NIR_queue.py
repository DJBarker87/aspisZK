from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[('lean','NIR_Driver'),('link','NIR_Driver'),('lean','NIR_ProofDriver'),('link','NIR_ProofDriver'),('audit','fixtures'),('audit','scan')]+[('audit','batch'+str(i))for i in range(32)]
for i,(kind,target) in enumerate(jobs,3):
 r=subprocess.run([sys.executable,str(E/'NIR_run.py'),f'NIR_L{i:03}',kind,target])
 if r.returncode:
  print(f'NIR queue stopped at L{i:03}: exit {r.returncode}',flush=True);sys.exit(r.returncode)
