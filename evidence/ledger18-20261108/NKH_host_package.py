"""Losslessly package only owned uncompressed raw diagnostic copies."""
from pathlib import Path
import hashlib,lzma,json,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-ledger18-20261108')
assert Path.cwd()==B
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(B.glob('NEP_*_REACHABLE.txt')):
 assert p.is_file()and not p.is_symlink()
 raw=p.read_bytes();digest=hashlib.sha256(raw).hexdigest();q=Path(str(p)+'.xz');sha=Path(str(p)+'.sha256')
 if q.exists():assert hashlib.sha256(lzma.decompress(q.read_bytes())).hexdigest()==digest
 else:q.write_bytes(lzma.compress(raw,preset=6))
 sha.write_text(digest+'\n')
 assert lzma.decompress(q.read_bytes())==raw and sha.read_text().strip()==digest
 row=dict(original=str(p),uncompressed_sha256=digest,uncompressed_bytes=len(raw),xz=str(q),xz_sha256=H(q),xz_bytes=q.stat().st_size,removed_only_after_roundtrip_verification=True)
 p.unlink();rows.append(row)
result=dict(status='PASS',diagnostics=rows,removed_uncompressed_bytes=sum(r['uncompressed_bytes']for r in rows),compressed_bytes=sum(r['xz_bytes']for r in rows),cache_retained=True,compiled_objects_retained=True,source_receipts_retained=True,disk=shutil.disk_usage(B)._asdict())
(B/'NKH_HOST_PACKAGING.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(dict(status='PASS',diagnostics=len(rows),removed_uncompressed_bytes=result['removed_uncompressed_bytes'],free=result['disk']['free'])))
