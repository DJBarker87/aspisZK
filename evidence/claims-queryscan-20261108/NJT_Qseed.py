from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
paths=json.loads((B/'NJT_QPATHS.json').read_text()); pins=[]
for i,src in enumerate(paths[:2]):
 d=B/('NJT_Qseed'+str(i)); assert not d.exists(); shutil.copytree(src,d)
 for p in sorted(d.rglob('*')):
  if p.is_file(): pins.append(dict(path=str(p),source=str(Path(src)/p.relative_to(d)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 paths[i]=str(d)
paths.insert(0,str(B/'NJT_Q_objects')); (B/'NJT_QPATHS.json').write_text(json.dumps(paths))
(B/'NJT_QSEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(p['bytes'] for p in pins)),indent=2)); print('NJT query seed copied and hashed')
