from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for target in [f'NGI_CertificatePart{i:02}' for i in range(6)]+['NGI_RootStatements']:
 rs=[json.loads(f.read_text()) for f in E.glob('NGI_L*/receipt.json')]
 if any(r['module']==target and r['exit_status']==0 for r in rs):continue
 assert len(rs)>=23 and not any(r['exit_status'] for r in rs)
 i=max(int(r['attempt'][-3:]) for r in rs)+1;assert i<=30
 r=subprocess.run([sys.executable,str(E/'NGI_run.py'),f'NGI_L{i:03}','lean',target])
 if r.returncode:sys.exit(r.returncode)
