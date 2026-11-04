"""Store immutable attempt source snapshots once by SHA-256; preserve every byte."""
from pathlib import Path
import hashlib,os,json
E=Path(__file__).resolve().parent;D=E/'NGA_inputs';D.mkdir(exist_ok=True)
rows=[]
for p in sorted(E.glob('NGA_*/sources/**/*')):
 if not p.is_file()or p.is_symlink():continue
 data=p.read_bytes()
 if len(data)<2048:continue
 h=hashlib.sha256(data).hexdigest();q=D/(h+'.txt')
 if q.exists():assert q.read_bytes()==data
 else:q.write_bytes(data)
 p.unlink();p.symlink_to(os.path.relpath(q,p.parent));assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 rows.append(dict(path=str(p.relative_to(E)),blob=str(q.relative_to(E)),sha256=h,bytes=len(data)))
(E/'NGA_SNAPSHOT_DEDUP.json').write_text(json.dumps(dict(new_symlinks=rows,inputs_excluded=False),indent=2)+'\n')
print(json.dumps(dict(snapshots=len(rows),unique_blobs=len(list(D.iterdir())))))
