from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(9,'lean','NIC_DriverPackets'),(10,'lean','NIC_COMBINED_IMPORT'),(11,'lean','NIC_ProofDriver'),(12,'link','NIC_ProofDriver'),(13,'audit','fixtures'),(14,'audit','batch0'),(15,'audit','scan')]
for i,kind,target in jobs:
 a=f'NIC_L{i:03d}'
 p=subprocess.run(['python3',str(E/'NIC_run.py'),a,kind,target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(p.stdout+p.stderr)
 f=E/a/'receipt.json'
 if not f.exists():print(a,'prelaunch failure',flush=True);break
 r=json.loads(f.read_text());print(a,kind,target,r['exit_status'],r['wall_seconds'],flush=True)
 if r['exit_status']:break
