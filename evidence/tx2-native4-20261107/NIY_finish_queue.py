"""Own serial final gates; stop on any nonzero status, never resubmit."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(91,'lean','NIY_COMBINED_IMPORT'),(92,'lean','NIY_ProofDriver'),(93,'link','NIY_ProofDriver'),(94,'lean','NIY_Driver'),(95,'link','NIY_Driver'),(96,'audit','fixtures'),(97,'audit','all'),(98,'audit','scan'),(99,'finalcheck','final')]
for n,kind,target in jobs:
 a=f'NIY_L{n:03d}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIY_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json';receipt=json.loads(p.read_text()) if p.exists() else {}
 print(json.dumps(dict(attempt=a,kind=kind,exit=r.returncode,receipt_exit=receipt.get('exit_status'),wall_seconds=receipt.get('wall_seconds'),peak_rss_kib=receipt.get('peak_rss_kib'))),flush=True)
 if r.returncode:sys.exit(r.returncode)
