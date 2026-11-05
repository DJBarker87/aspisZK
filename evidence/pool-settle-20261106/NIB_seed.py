"""Reproduce the small export seed; never modifies predecessor caches."""
from pathlib import Path
import hashlib,json,shutil,subprocess,lzma,sys
B=Path('/home/dombarker/project-offloads/codex-cx-pool-settle-20261106')
C=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104')
# Run on host with NIB_SEED.json (the committed hash/path inputs) as argument.
inputs=json.loads(Path(sys.argv[1]).read_text())
B.mkdir(exist_ok=True)
with (B/'NIB_RESEED_ADMISSION.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NIB_RESEED_ADMISSION.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((B/'NIB_RESEED_ADMISSION.json').read_text())
if r.returncode!=0 or ad.get('allowed') is not True:raise SystemExit(r.returncode or 78)
C.mkdir(exist_ok=True)
for row in inputs['imports']:
 src=Path(row['source']);dst=Path(row['path'])
 assert dst.parent==C
 raw=src.read_bytes();assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']
 if dst.exists():assert hashlib.sha256(dst.read_bytes()).hexdigest()==row['sha256']
 else:shutil.copy2(src,dst)
print(json.dumps(dict(seed_bytes=sum(x['bytes'] for x in inputs['imports']),objects=len(inputs['imports']))))
