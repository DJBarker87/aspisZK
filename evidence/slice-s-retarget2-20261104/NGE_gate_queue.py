"""Serial focused combined import, admitted driver builds, and coherence gates."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[('lean','NGE_COMBINED_IMPORT'),('lean','NGE_ProofDriver'),('link','NGE_ProofDriver'),('lean','NGE_Driver'),('link','NGE_Driver'),('audit','fixtures'),('audit','scan')]
for idx,(kind,target) in enumerate(jobs,32):
 a=f'NGE_L{idx:03}';r=subprocess.run([sys.executable,str(E/'NGE_run.py'),a,kind,target],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,kind,target,r.returncode,r.stdout[-600:],flush=True)
 if r.returncode:sys.exit(r.returncode)
