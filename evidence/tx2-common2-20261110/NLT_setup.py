from pathlib import Path
import hashlib,json,shutil,subprocess,sys
assert shutil.disk_usage('/home/dombarker/project-offloads').free>=40_000_000_000,'DISK WAIT required'
B=Path('/home/dombarker/project-offloads/codex-cx-tx2-common2-20261110');B.mkdir(exist_ok=True)
with (B/'NLT_setup-reservation.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NLT_setup-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=B/'NLT_setup-reservation.json';a=json.loads(p.read_text());assert r.returncode==0 and a.get('allowed') is True,(r.returncode,a)
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104');dest=B/'NLT_seed_20261110';dest.mkdir(exist_ok=True)
rows=[]
for src in [Path('/home/dombarker/project-offloads/codex-cx-tx2-common-20261110/NLP_exports_final_20261110'),Path('/home/dombarker/project-offloads/codex-cx-tx2-native11-20261109/NLB_exports_20261109'),Path('/home/dombarker/project-offloads/codex-cx-batch-merkle6-20261110/NLN_exports_final_20261110'),Path('/home/dombarker/project-offloads/codex-cx-tx2-resume2-20261109/NKU_exports_final_20261109'),Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLO_20261110/NLO_exports_20261110')]:
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=dest/p.relative_to(src)
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2(B.parent/'codex-cx-sound-int2-20261025'/n,B/n)
for n in ['NLT_objects','NLT_generated','NLT_tmp']:(B/n).mkdir(exist_ok=True)
x=dict(seed=rows,bytes=sum(r['bytes'] for r in rows),admission=a,exit=r.returncode)
(B/'NLT_SEED.json').write_text(json.dumps(x,indent=2));print(json.dumps(dict(seed_files=len(rows),seed_bytes=x['bytes'])))
