from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-tx2-resume-20261108');B.mkdir(exist_ok=True)
free=shutil.disk_usage(B).free
assert free>=40_000_000_000,free
with (B/'NKK_setup-reservation.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NKK_setup-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((B/'NKK_setup-reservation.json').read_text());assert r.returncode==0 and a.get('allowed') is True,(r.returncode,a)
rows=[];dest=B/'NKK_seed';dest.mkdir(exist_ok=True)
for src in [Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKH_20261108/NKH_exports_20261108'),Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJU_exports_20261108')]:
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=dest/p.relative_to(src)
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
shutil.copy2(B.parent/'codex-cx-tx2-native8-20261108/S2W_run_host.py',B/'S2W_run_host.py')
for n in ['NKK_objects','NKK_generated','NKK_tmp']:(B/n).mkdir(exist_ok=True)
x=dict(seed=rows,bytes=sum(z['bytes'] for z in rows),admission=a,free_bytes=free)
(B/'NKK_SEED.json').write_text(json.dumps(x,indent=2));print(json.dumps(dict(files=len(rows),bytes=x['bytes'])))
