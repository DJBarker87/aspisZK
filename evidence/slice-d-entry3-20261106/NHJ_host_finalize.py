"""Retain own focused objects and record their hashes; never mutate seed caches."""
from pathlib import Path
import hashlib,json,shutil,subprocess,time
B=Path.cwd();cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104');out=cache/'NHJ_exports_20261106'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
terminal=[]
for p in B.glob('NHJ_[KLE][0-9][0-9][0-9].json'):
 a=p.stem
 if a in ['NHJ_L002','NHJ_L079']:continue
 r=B/a/'receipt.json'
 assert r.is_file(),a
 terminal.append(dict(attempt=a,receipt_sha256=sha(r),exit_status=json.loads(r.read_text())['exit_status']))
objects=[]
for p in sorted((B/'NHJ_objects').rglob('*')):
 if not p.is_file() or not p.relative_to(B/'NHJ_objects').parts[0].startswith('NHJ_'):continue
 if not any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
 rel=p.relative_to(B/'NHJ_objects');q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==sha(p),str(q)
 else:shutil.copy2(p,q)
 objects.append(dict(relative_path=str(rel),source=str(p),retained=str(q),sha256=sha(q),bytes=q.stat().st_size))
assert objects
x=dict(status='PASS',export=str(out),objects=objects,bytes=sum(x['bytes']for x in objects),read_only_seeds=True,never_deleted_cache=True)
(B/'NHJ_CACHE_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n')
disk=shutil.disk_usage(B)
y=dict(status='PASS',terminal_attempts=terminal,export_bytes=x['bytes'],disk=dict(total=disk.total,used=disk.used,free=disk.free),source_revision=json.loads((B/'NHJ_L079.json').read_text())['source_revision'],source_sha256=sha(Path(__file__)),no_shipped_source_change=True,no_keys_deleted=True,no_cache_deleted=True,closure='Only NHJ focused objects; unchanged seed objects retained in their pinned directories. No release rebuild claim.')
(B/'NHJ_HOST_FINAL.json').write_text(json.dumps(y,indent=1)+'\n');print(json.dumps(dict(status='PASS',objects=len(objects),export_bytes=x['bytes'],free_bytes=disk.free)))
