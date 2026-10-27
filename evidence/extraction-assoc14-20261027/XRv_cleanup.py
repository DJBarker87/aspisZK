from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
host='dombarker@100.108.41.90'
code='''from pathlib import Path
import hashlib,json,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc14-20261027')
P=B/'XRv_objects'
rows=[dict(path=str(p.relative_to(B)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(P.rglob('*')) if p.is_file()]
r=dict(objects=rows,count=len(rows),bytes=sum(x['bytes'] for x in rows),retained_sources=True,shared_paths_removed=False,keys_touched=False)
(B/'XRv_CLEANUP.json').write_text(json.dumps(r,indent=2)+'\\n')
shutil.rmtree(P)
print(json.dumps(r))
'''
r=subprocess.run(['ssh',host,'python3 - <<\'PY\'\n'+code+'\nPY'],capture_output=True,text=True,check=True)
(E/'XRv_CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
x=json.loads((E/'XRv_CLEANUP.json').read_text());print({k:x[k] for k in ['count','bytes','shared_paths_removed','keys_touched']})
