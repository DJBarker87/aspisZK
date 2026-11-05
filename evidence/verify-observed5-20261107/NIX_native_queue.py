from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for i in range(4,16):
 a=f'NIX_K{i:03}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'missing receipt; STOP',flush=True);break
 x=json.loads(p.read_text());print(a,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status'] in [124,137] or 'Timed out' in (E/a/'stdout.log').read_text():print('STOP timed-out shape; split before continuation',flush=True);break
