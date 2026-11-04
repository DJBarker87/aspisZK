"""Store repeated large evidence inputs once; preserve all logical receipt paths."""
from pathlib import Path
import hashlib,json,os,collections
E=Path(__file__).resolve().parent;groups=collections.defaultdict(list)
for p in E.rglob('*'):
 if p.is_file() and not p.is_symlink() and p.stat().st_size>=131072 and 'NFM_inputs' not in p.parts:
  groups[hashlib.sha256(p.read_bytes()).hexdigest()].append(p)
D=E/'NFM_inputs';D.mkdir(exist_ok=True);rows=[]
for h,paths in groups.items():
 if len(paths)<2:continue
 b=paths[0].read_bytes();q=D/h
 if q.exists():assert q.read_bytes()==b
 else:q.write_bytes(b)
 for p in paths:
  assert p.read_bytes()==b
  p.unlink();p.symlink_to(os.path.relpath(q,p.parent))
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 rows.append(dict(sha256=h,bytes=len(b),stored=str(q.relative_to(E)),logical_paths=[str(p.relative_to(E)) for p in paths]))
# Preserve prior records when run again; no symlink is rewritten.
P=E/'NFM_INPUT_STORAGE.json';prior=json.loads(P.read_text()) if P.exists() else []
P.write_text(json.dumps(prior+rows,indent=1)+'\n');print('deduplicated',sum(len(r['logical_paths']) for r in rows),'paths; saved',sum((len(r['logical_paths'])-1)*r['bytes'] for r in rows),'bytes')
