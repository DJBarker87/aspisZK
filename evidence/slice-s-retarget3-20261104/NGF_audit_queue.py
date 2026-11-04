"""Sequential audit preparation and non-overlapping raw partitions, one scope each."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[('lean','NGF_ProofDriver'),('lean','NGF_Driver'),('link','NGF_ProofDriver'),('link','NGF_Driver'),('audit','fixtures'),('audit','scan')]
jobs += [('audit','batch'+str(i)) for i in range(len(json.loads((E/'NGF_AUDIT_ROOTS.json').read_text())['groups']))]
for kind,target in jobs:
 receipts=[json.loads(f.read_text()) for f in E.glob('NGF_L*/receipt.json')]
 if any(r['kind']==kind and r['module']==target and r['exit_status']==0 for r in receipts):continue
 i=max(int(f.name[5:8]) for f in E.glob('NGF_L[0-9][0-9][0-9].json'))+1
 assert i<=110,('budget exhausted',kind,target)
 r=subprocess.run([sys.executable,str(E/'NGF_run.py'),f'NGF_L{i:03}',kind,target])
 if r.returncode:sys.exit(r.returncode)
