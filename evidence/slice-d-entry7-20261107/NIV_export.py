from NIV_transport import *
import hashlib
mods=[l[7:]for l in (E/'NIV_COMBINED_IMPORT.lean').read_text().splitlines()if l.startswith('import NIV_')]+['NIV_COMBINED_IMPORT']
r=ssh('python3',f'''from pathlib import Path
import hashlib,json,shutil
b=Path({B!r});mods={mods!r};files=[]
for m in mods:
 p=b/'NIV_objects'/(m+'.olean');assert p.is_file()
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():files.append(z)
rows=[dict(path=str(p.relative_to(b/'NIV_objects')),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)for p in sorted(files)]
tree=hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest();d=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104')/('NIV_exports_20261107_'+tree[:12]);d.mkdir(exist_ok=True)
for p in files:
 q=d/p.relative_to(b/'NIV_objects');q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
x=dict(path=str(d),tree_sha256=tree,bytes=sum(r['bytes']for r in rows),files=rows,modules=mods,upstream='NIS_exports_20261107_443ef40bff98; see NIV_SEED manifest',target_established=False,new_composed_rows=0)
(d/'NIV_EXPORT.json').write_text(json.dumps(x,indent=1)+'\\n');print(json.dumps(x))
''');assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NIV_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:x[k]for k in ['path','bytes','tree_sha256']}))
