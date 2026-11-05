from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for a in ['NIH_L062','NIH_L060','NIH_L063','NIH_L064','NIH_L065','NIH_L066','NIH_L067','NIH_L068']:
 with (E/(a+'-client.log')).open('w') as log:r=subprocess.run([sys.executable,str(E/'NIH_run.py'),a],stdout=log,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'missing receipt STOP',flush=True);sys.exit(1)
 rc=json.loads(p.read_text());print(json.dumps(dict(attempt=a,exit=r.returncode,wall=rc['wall_seconds'],rss=rc['peak_rss_kib'],axioms=rc['print_axioms'])),flush=True)
 if r.returncode:print((E/a/'stdout.log').read_text()[:3000],flush=True);sys.exit(1)
