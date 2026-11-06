from pathlib import Path
import json,shutil,hashlib
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJG_exports_20261107')
D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJM_seed_20261108')
assert not D.exists()
shutil.copytree(P,D)
pins=[dict(path=str(p),source=str(P/p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(D.rglob('*')) if p.is_file()]
paths=json.loads((B/'NJM_PATHS.json').read_text());paths=[str(D) if x==str(P) else x for x in paths];paths.insert(0,str(B/'NJM_objects'))
(B/'NJM_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
(B/'NJM_SEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(p['bytes'] for p in pins),cargo_target_dir=str(B/'NJM_target')),indent=2)+'\n')
print('NJM seed copied and hashed')
