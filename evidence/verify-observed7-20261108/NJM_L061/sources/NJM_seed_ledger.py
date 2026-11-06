from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NJK_20261108/NJK_exports_20261108')
D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJM_NJK_20261108')
assert not D.exists();shutil.copytree(P,D)
pins=[dict(path=str(p),source=str(P/p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(D.rglob('*')) if p.is_file()]
paths=json.loads((B/'NJM_PATHS.json').read_text());extra=json.loads((B/'NJM_LEDGER_PATH_INPUT.json').read_text());paths.insert(2,str(D))
for p in extra:
 if p.endswith('/NJK_objects'):continue
 if p not in paths:paths.append(p)
(B/'NJM_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
(B/'NJM_LEDGER_SEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(p['bytes'] for p in pins),cargo_target_dir=str(B/'NJM_target')),indent=2)+'\n')
print('NJM ledger14 export added after predecessor seed; hashes retained')
