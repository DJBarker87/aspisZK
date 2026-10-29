from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag5-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((D/'final-post.json').read_text())['mismatches']==[]
rows=[]
for p in (D/'objects').rglob('*'):
 if not (p.is_symlink() or p.is_file()):continue
 assert p.name.endswith(('.olean','.olean.server','.olean.private','.ir')),p
 rows.append(dict(path=str(p),symlink=p.is_symlink(),target=str(p.resolve()) if p.is_symlink() else None,sha256=sha(p),bytes=p.stat().st_size));p.unlink()
p=D/'native-controls'
if p.exists():rows.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,symlink=False));p.unlink()
(D/'cleanup.json').write_text(json.dumps(dict(removed=rows,retained='all sources, raw evidence, shared cache targets and all keys; no wallet/key operations'),indent=2)+'\n');print('removed only private compiled artifacts/links',len(rows))
