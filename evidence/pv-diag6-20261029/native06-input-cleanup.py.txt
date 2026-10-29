from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag6-20261029');rows=[]
for p in (D/'objects').rglob('*'):
 if not p.is_file() and not p.is_symlink():continue
 assert p.suffix in {'.olean','.server','.private','.ir'},p
 rows.append(dict(path=str(p),symlink=p.is_symlink(),target=str(p.resolve()),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 p.unlink()
p=D/'native-prefix'
if p.exists():
 rows.append(dict(path=str(p),symlink=False,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
(D/'cleanup.json').write_text(json.dumps(dict(removed=rows,keys='No wallet/account/nonce key created, touched, or removed; sources and evidence retained; shared targets untouched.'),indent=2)+'\n');print('removed own compiled artifacts/links',len(rows))
