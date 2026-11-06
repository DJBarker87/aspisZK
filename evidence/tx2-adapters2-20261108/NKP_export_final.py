from pathlib import Path
import shutil,hashlib,json
b=Path.cwd();dst=b/'NKP_exports_final_20261108';assert not dst.exists();dst.mkdir();rows=[]
for p in sorted((b/'NKP_objects').glob('NKP_*')):
 if p.is_file() and ('.olean' in p.name or p.suffix=='.ir'):
  q=dst/p.name;shutil.copy2(p,q);rows.append(dict(source=str(p),path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
assert rows
obj=dict(destination=str(dst),files=rows,bytes=sum(x['bytes'] for x in rows),CARGO_TARGET_DIR=str(b/'NKP_target'),TMPDIR=str(b/'NKP_tmp'),retained=True)
(b/'NKP_EXPORT_FINAL.json').write_text(json.dumps(obj,indent=1)+'\n')
print(json.dumps(dict(export_bytes=obj['bytes'],export_files=len(rows),destination=str(dst))))
