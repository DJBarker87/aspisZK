"""Retain each large exact input/output once; preserve original path/hash aliases."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent;groups={};rows=[]
for p in E.rglob('*'):
 if p.is_file()and p.stat().st_size>=1_000_000 and not p.name.endswith(('.xz','.b64.txt'))and p.name not in ['NJB_DEDUP.json']and p.suffix not in ['.lean']:
  h=hashlib.sha256(p.read_bytes()).hexdigest();groups.setdefault(h,[]).append(p)
for h,paths in groups.items():
 if len(paths)<2:continue
 paths.sort(key=lambda p:(len(p.relative_to(E).parts),str(p)));keep=paths[0]
 for p in paths[1:]:
  rows.append(dict(path=str(p.relative_to(E)),sha256=h,retained=str(keep.relative_to(E)),bytes=p.stat().st_size));p.unlink()
# Payload transport copies also retain one exact content-addressed source.
for p in E.rglob('*.b64.txt'):
 if p.stat().st_size<1_000_000:continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 others=[q for q in E.rglob(p.name)if q!=p and q.is_file()and q.stat().st_size==p.stat().st_size and hashlib.sha256(q.read_bytes()).hexdigest()==h]
 if not others:continue
 keep=min([p]+others,key=lambda q:(len(q.relative_to(E).parts),str(q)))
 if p!=keep:rows.append(dict(path=str(p.relative_to(E)),sha256=h,retained=str(keep.relative_to(E)),bytes=p.stat().st_size));p.unlink()
old=E/'NJB_DEDUP.json';prior=json.loads(old.read_text())if old.exists()else[]
old.write_text(json.dumps(prior+rows,indent=1));print(json.dumps(dict(aliases=len(rows),saved_bytes=sum(r['bytes']for r in rows))))
