from pathlib import Path
import json,shutil,hashlib
B=Path.cwd();export=json.loads((B/'NKA_EXPORT.json').read_text());dirs=[Path(export['directory']),Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKA_exports_20261108'),B/'NKA_objects',B/'NKA_NJT_seed',B/'NKA_NJW_seed',B/'NKA_target']
rows=[]
for directory in dirs:
 assert directory.is_dir(),str(directory)
 files=[p for p in directory.rglob('*') if p.is_file()]
 rows.append(dict(directory=str(directory),files=len(files),bytes=sum(p.stat().st_size for p in files),retained=True))
for r in export['files']:assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256']
for p in B.glob('NKA*/__pycache__'):
 if p.is_dir():shutil.rmtree(p)
report=dict(status='PASS',retained=rows,deleted_cache=False,free_bytes=shutil.disk_usage(B).free,total_bytes=shutil.disk_usage(B).total,cargo_target_dir=str(B/'NKA_target'),phase1='Superseded for129 native initialization; retained only for provenance, not final candidate credit')
(B/'NKA_RETENTION.json').write_text(json.dumps(report,indent=2)+'\n')
print('NKA both exports, objects, seeds and small native target retained; disk inventoried')
