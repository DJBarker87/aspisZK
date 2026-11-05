from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
remote='''from pathlib import Path
import json,hashlib,shutil,os
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-finish-20261105');C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104');D=C/'NGM_exports_20261105';D.mkdir(exist_ok=True);rows=[]
for source in sorted((B/'NGM_objects').rglob('*')):
 if not source.is_file():continue
 rel=source.relative_to(B/'NGM_objects');dest=D/rel;dest.parent.mkdir(parents=True,exist_ok=True);digest=hashlib.sha256(source.read_bytes()).hexdigest()
 if dest.exists():assert hashlib.sha256(dest.read_bytes()).hexdigest()==digest
 else:shutil.copy2(source,dest)
 assert hashlib.sha256(dest.read_bytes()).hexdigest()==digest
 rows.append(dict(file=str(rel),sha256=digest,bytes=source.stat().st_size))
s=os.statvfs(B);x=dict(status='retained; never delete own cache',workspace=str(B),cache=str(C),exports=str(D),export_files=len(rows),export_bytes=sum(r['bytes']for r in rows),objects=rows,disk=dict(bytes=s.f_blocks*s.f_frsize,free_bytes=s.f_bavail*s.f_frsize),seed_manifest='NGM_CACHE_IMPORTS.json.xz',seed_bytes=7586865704,seed_files=29968,deletions=[]);(B/'NGM_RETENTION.json').write_text(json.dumps(x,indent=1));print(json.dumps(x))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3'],input=remote,capture_output=True,text=True);assert r.returncode==0,r.stderr;x=json.loads(r.stdout);(E/'NGM_RETENTION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:x[k]for k in ['status','export_files','export_bytes','disk']}))
