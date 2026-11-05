from pathlib import Path
import json,shutil,hashlib
B=Path(__file__).resolve().parent;source=Path('/home/dombarker/project-offloads/codex-cx-slice-d-parser2-cache-20261104/NGO_exports_20261105');dest=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NIH_seed_20261107/NIH_NGO')
shutil.copytree(source,dest)
pins=[dict(path=str(p),source=str(source/p.relative_to(dest)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(dest.rglob('*')) if p.is_file()]
paths=json.loads((B/'NIH_PATHS.json').read_text());paths.insert(1,str(dest))
prior=json.loads((B/'NIH_NGO_PATHS.json').read_text())
# Append retained cache dependencies without changing established canonical priority.
for p in prior:
 if p not in paths and 'codex-cx-slice-d-parser2-20261105' not in p:paths.append(p)
(B/'NIH_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n');(B/'NIH_DECODER_SEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(p['bytes'] for p in pins)),indent=2)+'\n');print('decoder seed bytes',sum(p['bytes'] for p in pins))
