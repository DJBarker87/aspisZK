"""Lossless local packaging only; no proof/gate is rerun."""
from pathlib import Path
import lzma,hashlib,json,shutil
E=Path(__file__).resolve().parent;count=0
for p in list(E.rglob('*')):
 if not p.is_file()or p.suffix not in ['.log','.time']:continue
 raw=p.read_bytes();q=Path(str(p)+'.xz');h=hashlib.sha256(raw).hexdigest()
 if q.exists():assert lzma.decompress(q.read_bytes())==raw
 else:q.write_bytes(lzma.compress(raw,preset=6))
 Path(str(p)+'.sha256').write_text(h+'\n');p.unlink();count+=1
for p in list(E.rglob('__pycache__')):shutil.rmtree(p)
large=[str(p.relative_to(E))for p in E.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024];assert not large,large
(E/'NLZ_HYGIENE.json').write_text(json.dumps(dict(status='PASS',newly_packaged_logs=count,large_files=[],raw_bytes_preserved=True,generated_C_bytes_preserved=True,scope_or_proof_replay=False),indent=2))
print(json.dumps(dict(packaged_logs=count,large_files=0,raw_bytes_preserved=True)))
