from pathlib import Path
import hashlib,json,shutil
b=Path.cwd();p=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_native_seed');rows=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 q=p/n;r=b/'NJX_native'/n;shutil.copyfile(q,r);rows.append(dict(source=str(q),target=str(r),sha256=hashlib.sha256(r.read_bytes()).hexdigest(),bytes=r.stat().st_size))
(b/'NJX_GATE_PINS.json').write_text(json.dumps(rows,indent=1));print('unchanged walker/memory C source copied and pinned')

# Exclude the unused experimental unprefixed dependency from the combined path.
u=b/'NJX_unused';u.mkdir(exist_ok=True)
for q in (b/'NJX_objects').glob('RawPoseidonExternalRows.*'):
 if q.is_file():q.rename(u/q.name)
m=json.loads((b/'NJX_PREDECESSOR_EXPORT.json').read_text());checks=[]
for entry in m.get('seed_files',[]):
 q=Path(entry['path']);assert hashlib.sha256(q.read_bytes()).hexdigest()==entry['sha256'],str(q)
 checks.append(dict(path=str(q),sha256=entry['sha256'],bytes=q.stat().st_size))
(b/'NJX_IMPORTED_PIN_CHECK.json').write_text(json.dumps(dict(readonly_seed_files=checks,total_readonly_seed_bytes=sum(x['bytes']for x in checks))))
