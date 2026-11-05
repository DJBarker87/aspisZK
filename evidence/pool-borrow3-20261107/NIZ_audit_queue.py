from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(22,'lean','NIZ_Driver'),(23,'lean','NIZ_ProofDriver'),(24,'link','NIZ_Driver'),(25,'link','NIZ_ProofDriver'),(26,'audit','fixtures'),(27,'audit','batch0'),(28,'audit','scan')]
for number,kind,target in jobs:
 a=f'NIZ_L{number:03d}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIZ_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json';assert p.exists(),'Missing receipt; recover read-only, never resubmit'
 d=json.loads(p.read_text());print(a+' '+target+' exit '+str(d['exit_status']),flush=True)
 if r.returncode or d['exit_status']:raise SystemExit('Changed inputs or isolated diagnostic required before further launch')
