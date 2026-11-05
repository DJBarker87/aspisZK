from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for i,target in [(33,'NIX_PrefixFrames'),(34,'NIX_CircleLogLaw')]:
 a=f'NIX_L{i:03}';subprocess.run(['python3',str(E/'NIX_config.py'),a,'lean',target],check=True)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 receipt=E/a/'receipt.json'
 if not receipt.exists():print(a,'NO RECEIPT STOP',flush=True);break
 x=json.loads(receipt.read_text());print(a,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status'] in [124,137]:break
