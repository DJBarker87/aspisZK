"""Execute the committed focused manifest exactly once; stop on any failure."""
import json,subprocess,sys
from pathlib import Path
E=Path('evidence/pv-l2e-20261029')
x=json.load(open(E/'final-focused-manifest.json'))
for row in x['replay']:
 a=row['attempt'];m=row['module']
 with open(E/f'final-driver-{a}.log','w') as log:
  r=subprocess.run([sys.executable,'tools/pv-l2e-20261029/prepare.py',m],stdout=log,stderr=subprocess.STDOUT)
  if r.returncode:raise SystemExit(r.returncode)
  r=subprocess.run([sys.executable,'tools/pv-l2e-20261029/compile.py',str(a),m],stdout=log,stderr=subprocess.STDOUT)
 if r.returncode:
  print('STOP',a,m,r.returncode,flush=True);raise SystemExit(r.returncode)
 rec=json.load(open(E/f'receipt-{a}.json'))
 print('PASS',a,m,rec['wall'],rec['peak_rss_kbytes'],flush=True)
