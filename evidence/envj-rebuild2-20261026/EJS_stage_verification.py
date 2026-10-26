from pathlib import Path
import hashlib,json
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');src=J/'sources/R1Z/EJS_Verification.lean';assert not src.exists();b=(T/'EJS_Verification.lean').read_bytes();src.write_bytes(b)
rows=json.loads((T/'EJS_missing-sources.json').read_text());rows.append(dict(module='R1Z/EJS_Verification',workspace='joint',host_path=str(src),source_sha256=hashlib.sha256(b).hexdigest(),blob='new EJS_Verification.lean committed source',revision=(T/'EJS_launch-revision.txt').read_text().strip(),bytes=len(b)));(T/'EJS_missing-sources.json').write_text(json.dumps(rows,indent=2)+'\n');print('staged new prefixed launcher smoke source')
