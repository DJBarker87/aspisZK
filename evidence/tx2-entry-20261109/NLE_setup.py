from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-tx2-entry-20261109');B.mkdir(exist_ok=True)
free=shutil.disk_usage(B).free
assert free>=40_000_000_000,free
with (B/'NLE_setup-reservation.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NLE_setup-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((B/'NLE_setup-reservation.json').read_text());assert r.returncode==0 and a.get('allowed') is True,(r.returncode,a)
rows=[]
for label,source in [('NKU','codex-cx-tx2-resume2-20261109/NKU_exports_final_20261109'),('NJN','codex-cx-slice-d-prepared-cache-20261104/NJN_exports_20261108_ee4038fa99e9'),('NKW','codex-cx-ledger8-cache-20261104/NKW_20261109/NKW_exports_20261109')]:
 src=B.parent/source;assert src.is_dir(),src
 dest=B/'NLE_seed'/label;dest.mkdir(parents=True,exist_ok=True)
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=dest/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
shutil.copy2(B.parent/'codex-cx-tx2-resume2-20261109/S2W_run_host.py',B/'S2W_run_host.py')
for n in ['NLE_objects','NLE_generated','NLE_tmp','NLE_target']:(B/n).mkdir(exist_ok=True)
x=dict(seed=rows,bytes=sum(z['bytes'] for z in rows),admission=a,free_bytes=free)
(B/'NLE_SEED.json').write_text(json.dumps(x,indent=2));print(json.dumps(dict(files=len(rows),bytes=x['bytes'])))
