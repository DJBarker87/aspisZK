from pathlib import Path
import subprocess,json,shutil,sys,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair5-20261107')
with (B/'NIQ_NATIVE_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NIQ_NATIVE_SEED-admission.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((B/'NIQ_NATIVE_SEED-admission.json').read_text())
if r.returncode or ad.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,reservation=ad)));sys.exit(78)
P=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair4-20261107/NIG_src')
shutil.copytree(P,B/'NIQ_src',dirs_exist_ok=True,ignore=shutil.ignore_patterns('target','__pycache__'))
rows=[dict(path=str(p.relative_to(P)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)for p in sorted(P.rglob('*')) if p.is_file() and 'target' not in p.parts]
x=dict(admission=ad,source=str(P),bytes=sum(r['bytes'] for r in rows),files=rows)
(B/'NIQ_NATIVE_SEED.json').write_text(json.dumps(x,indent=2));print(json.dumps(x))
