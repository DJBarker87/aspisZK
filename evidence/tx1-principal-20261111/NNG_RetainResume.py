"""Pin accepted objects in place; never delete or overwrite any cache."""
from pathlib import Path
import json,hashlib
B=Path.cwd();selected=json.loads((B/'NNG_Resume_AUDIT_ROOTS.json').read_text())['selected'];rows=[]
for module,item in sorted(selected.items()):
 rows.append((module,B/'NNG_R4_objects'/(module+'.olean'),item['sha256'],item['attempt']))
for item in json.loads((B/'NNG_WRAPPER_REPLAY_PLAN.json').read_text()):
 receipt=B/item['attempt']/'receipt.json'
 if not receipt.is_file():continue
 r=json.loads(receipt.read_text());assert r['exit_status']==0
 assert r['source_hashes'][item['private_source']]==item['sha256']
 rows.append((item['module'],B/'NNG_WrapperR4_objects'/(item['module']+'.olean'),item['sha256'],item['attempt']))
results=[]
for module,obj,source,attempt in rows:
 assert obj.is_file(),obj
 files=[]
 for q in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if q.is_file():files.append({'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size})
 results.append({'module':module,'source_sha256':source,'receipt':attempt+'/receipt.json','files':files})
(B/'NNG_RESUME_RETAINED_OBJECTS.json').write_text(json.dumps({'status':'retained in place, no deletion','modules':results},indent=2))
print(json.dumps({'modules':len(results),'files':sum(len(r['files'])for r in results),'bytes':sum(q['bytes']for r in results for q in r['files'])}))
