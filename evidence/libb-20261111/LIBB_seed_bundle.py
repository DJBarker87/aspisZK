"""Copy the retained merged TX1 bundle export, verifying every imported byte."""
from pathlib import Path
import subprocess,json,hashlib,time
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import hashlib,json,shutil
source=Path('/home/dombarker/project-offloads/codex-cx-lib-20261111/LIB_exports_bundle_20261111')
dest=Path('/home/dombarker/project-offloads/codex-cx-libb-20261111/LIBB_seedBundle')
files=[]
for p in sorted(source.rglob('*')):
 if not p.is_file():continue
 assert any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']),str(p)
 q=dest/p.relative_to(source);q.parent.mkdir(parents=True,exist_ok=True)
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 else:shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 files.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
print(json.dumps(dict(export=str(source),destination=str(dest),files=files,disk=shutil.disk_usage(dest)._asdict())))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 with (E/'LIBB_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(event='seed_merged_bundle',retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
result=json.loads(r.stdout);assert result['disk']['free']>=40_000_000_000
(E/'LIBB_BUNDLE_REUSE.json').write_text(json.dumps(result,indent=1)+'\n')
p=E/'LIBB_PATHS.json';paths=json.loads(p.read_text())
if result['destination'] not in paths:paths.insert(0,result['destination']);p.write_text(json.dumps(paths,indent=1)+'\n')
print(json.dumps(dict(files=len(result['files']),bytes=sum(x['bytes'] for x in result['files']),free=result['disk']['free'])))
