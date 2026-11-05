from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n in range(84,91):
 a=f'NIH_L{n:03}'
 with (E/(a+'-client.log')).open('w') as log:r=subprocess.run([sys.executable,str(E/'NIH_run.py'),a],stdout=log,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'missing receipt STOP',flush=True);sys.exit(1)
 rc=json.loads(p.read_text());print(json.dumps(dict(attempt=a,exit=r.returncode,wall=rc['wall_seconds'],rss=rc['peak_rss_kib'])),flush=True)
 if r.returncode:print((E/a/'stdout.log').read_text()[-4000:],flush=True);sys.exit(1)
