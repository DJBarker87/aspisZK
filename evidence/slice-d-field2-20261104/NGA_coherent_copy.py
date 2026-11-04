from pathlib import Path
import json,hashlib,shutil
P=Path('/home/dombarker/project-offloads');C=P/'codex-cx-slice-d-field2-cache-20261104'
rows=[]
for source in (P/'codex-cx-ledger7-cache-20261104/NFX_exports_20261104').rglob('*'):
 if not source.is_file():continue
 dest=C/'NGA_NFX_imports_20261104'/source.relative_to(source.parents[0])
 dest.parent.mkdir(exist_ok=True,parents=True);dest.write_bytes(source.read_bytes())
 rows.append(dict(source=str(source),destination=str(dest),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),bytes=source.stat().st_size))
print(json.dumps(rows,indent=1))
