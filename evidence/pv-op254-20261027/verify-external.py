from pathlib import Path
import json,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-pv-op254-20261027')
start=time.monotonic(); rows=[]
for x in json.loads((H/'external-object-manifest.json').read_text()):
 p=Path(x['path']); actual=hashlib.file_digest(p.open('rb'),'sha256').hexdigest() if p.exists() else None
 rows.append(dict(module=x['module'],path=str(p),expected=x['object_sha256'],actual=actual,match=actual==x['object_sha256']))
result=dict(wall_seconds=time.monotonic()-start,checked=len(rows),mismatches=[x for x in rows if not x['match']],objects=rows)
(H/'external-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='objects'}))
