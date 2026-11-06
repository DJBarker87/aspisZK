from pathlib import Path
import hashlib,json,shutil,subprocess,sys
B=Path('/home/dombarker/project-offloads/codex-cx-tx2-native9-20261108');B.mkdir(exist_ok=True)
with (B/'NKE_setup-reservation.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NKE_setup-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=B/'NKE_setup-reservation.json';a=json.loads(p.read_text());assert r.returncode==0 and a.get('allowed') is True,(r.returncode,a)
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104');dest=C/'NKE_seed_20261108';dest.mkdir(exist_ok=True)
rows=[]
for src in [C/'NJU_exports_20261108',Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKC_20261108/NKC_exports_20261108')]:
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=dest/p.relative_to(src)
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['S2W_run_host.py']:
 shutil.copy2(B.parent/'codex-cx-sound-int2-20261025'/n,B/n)
for n in ['NKE_objects','NKE_generated','NKE_tmp']:(B/n).mkdir(exist_ok=True)
x=dict(seed=rows,bytes=sum(r['bytes'] for r in rows),admission=a,exit=r.returncode)
(B/'NKE_SEED.json').write_text(json.dumps(x,indent=2));print(json.dumps(x))
