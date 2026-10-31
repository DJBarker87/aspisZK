from pathlib import Path
import lzma,hashlib,json
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031');p=H/'PV_B3Q_TargetedCone2.llbc';raw=p.read_bytes();q=p.with_suffix('.llbc.xz');q.write_bytes(lzma.compress(raw,preset=3))
(H/'targeted2-cone-output.json').write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),compressed_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),compressed_bytes=q.stat().st_size),indent=2)+'\n')
