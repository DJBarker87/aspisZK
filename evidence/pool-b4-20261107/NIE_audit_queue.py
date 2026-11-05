from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[('NIE_L009','link','NIE_ProofDriver'),('NIE_L010','lean','NIE_Driver'),('NIE_L011','link','NIE_Driver'),('NIE_L012','audit','fixtures'),('NIE_L013','audit','batch0'),('NIE_L014','audit','scan')]
for a,kind,target in jobs:
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIE_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Audit client failure; details retained: '+a)
 x=json.loads(p.read_text());print(json.dumps({k:x[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
 if x['exit_status']:raise SystemExit('Audit review required; no unchanged rerun')
