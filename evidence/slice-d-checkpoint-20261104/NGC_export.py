from pathlib import Path
import shutil,json,hashlib,subprocess
b=Path.cwd();c=Path('/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-cache-20261104');dest=c/'NGC_exports_20261104';dest.mkdir(exist_ok=True);rows=[]
for src in sorted((b/'NGC_objects').rglob('*')):
 if not src.is_file():continue
 rel=src.relative_to(b/'NGC_objects')
 assert rel.parts[0].startswith('NGC_'),str(rel)
 out=dest/rel;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,out)
 assert out.read_bytes()==src.read_bytes()
 rows.append(dict(source=str(src),path=str(out),bytes=out.stat().st_size,sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
x=dict(status='PASS',destination=str(dest),bytes=sum(r['bytes']for r in rows),files=len(rows),objects=rows,seed_bytes=311428679,selected_closure_bytes=14813839856,cache_policy='Retain cache; do not delete it',disk_before_cleanup=subprocess.check_output(['df','-B1',str(b)],text=True))
(b/'NGC_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:v for k,v in x.items()if k!='objects'}))
