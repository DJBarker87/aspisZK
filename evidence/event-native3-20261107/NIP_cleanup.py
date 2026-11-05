from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();assert B==Path('/home/dombarker/project-offloads/codex-cx-event-native3-20261107')
x=json.loads((B/'NIP_EXPORT.json').read_text())
for r in x['objects']:assert hashlib.sha256(Path(r['destination']).read_bytes()).hexdigest()==r['sha256']
removed=[]
for name in ['NIP_objects','NIP_native','NIP_tmp']:
 p=B/name
 size=sum(z.stat().st_size for z in p.rglob('*') if z.is_file()) if p.exists() else 0
 if p.exists():shutil.rmtree(p)
 removed.append(dict(path=str(p),bytes=size))
print(json.dumps(dict(export_verified=True,removed=removed,cache_retained=True)))
