"""Remove only identified own compiler caches/test executables after final audit.
Unknown files are retained. No source, receipt, wallet or account key is removed.
"""
from pathlib import Path
import json,hashlib,shutil,sys,time
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028');start=time.monotonic();removed=[];retained=[]
for name in ['lean-objects','external-objects']:
 p=D/name
 if not p.exists():continue
 if p.is_symlink():retained.append(dict(path=str(p),reason='root symlink; no traversal'));continue
 entries=[q for q in p.rglob('*') if q.is_file() or q.is_symlink()]
 unknown=[str(q) for q in entries if not q.name.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.o','.so'))]
 if unknown:retained.append(dict(path=str(p),reason='unrecognized cache entry; retain by default',entries=unknown));continue
 size=sum(q.lstat().st_size for q in entries)
 shutil.rmtree(p);removed.append(dict(path=str(p),kind='compiler cache / own links to pinned external objects',files=len(entries),bytes_lstat=size))
for name in ['range-native','v260-constant-probe']:
 p=D/name
 if not p.exists():continue
 if p.is_symlink() or not p.is_file():retained.append(dict(path=str(p),reason='not identified regular executable'));continue
 raw=p.read_bytes()
 if raw[:4]!=b'\x7fELF':retained.append(dict(path=str(p),reason='not identified ELF executable'));continue
 removed.append(dict(path=str(p),kind='own optimized test executable',bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()));p.unlink()
j=dict(source_revision=sys.argv[1],removed=removed,retained=retained,wall_seconds=time.monotonic()-start,source_and_receipts_retained=True,wallet_account_keys_created=0,wallet_account_keys_removed=0,qualification='Final coherence/object hashes were measured before this cleanup. No compiled-cache reuse is claimed afterward. Shared external targets and other job directories were not mutated.')
(D/'cleanup-result.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
