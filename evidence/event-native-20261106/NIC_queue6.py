from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(62,'circle_pure'),(63,'circle_control'),(64,'line_pure'),(65,'line_control')]
for i,target in jobs:
 a=f'NIC_K{i:03d}'
 p=subprocess.run(['python3',str(E/'NIC_kani_run.py'),a,'kani',target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(p.stdout+p.stderr)
 receipt=E/a/'receipt.json'
 if not receipt.exists():print(a,'PRELAUNCH ERROR',flush=True);break
 r=json.loads(receipt.read_text());print(a,target,r['exit_status'],r['wall_seconds'],flush=True)
 if r['exit_status'] in [124,137] or 'timed out' in (E/a/'stdout.log').read_text().lower():print('review required',flush=True);break
