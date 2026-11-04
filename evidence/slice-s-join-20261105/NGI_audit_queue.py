from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
jobs=[('lean','NGI_ProofDriver'),('lean','NGI_Driver'),('link','NGI_ProofDriver'),('link','NGI_Driver'),('audit','fixtures'),('audit','scan')]+[('audit','batch'+str(i)) for i in range(16)]
for kind,target in jobs:
 rs=[json.loads(f.read_text()) for f in E.glob('NGI_L*/receipt.json')]
 if any(r['kind']==kind and r['module']==target and r['exit_status']==0 for r in rs):continue
 i=max([int(r['attempt'][-3:]) for r in rs],default=0)+1
 assert i<=30
 r=subprocess.run([sys.executable,str(E/'NGI_run.py'),f'NGI_L{i:03}',kind,target])
 if r.returncode:sys.exit(r.returncode)
