"""Retain byte-identical own Lean objects; no build, deletion or shared mutation."""
from pathlib import Path
import subprocess,json,time,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-libb-20261111'
code='''from pathlib import Path
import hashlib,json,shutil
b=Path(%r);dest=b/'LIBB_exports_20261111';dest.mkdir(exist_ok=True)
files=[]
for p in sorted((b/'LIBB_objects').rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(b/'LIBB_objects');q=dest/rel;q.parent.mkdir(parents=True,exist_ok=True)
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==sha,str(q)
 else:shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==sha
 files.append(dict(module=str(rel),path=str(q),sha256=sha,bytes=q.stat().st_size))
t=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin')
tools={n:dict(path=str(t/n),sha256=hashlib.sha256((t/n).read_bytes()).hexdigest())for n in ['lean','leanc','lake']}
out=dict(export=str(dest),objects=files,toolchain=tools,host_disk=shutil.disk_usage(b)._asdict(),deletions=0)
(b/'LIBB_EXPORT.json').write_text(json.dumps(out,indent=1)+'\\n');print(json.dumps(out))
'''%B
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with (E/'LIBB_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(event='retention_read_copy',retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);assert out['host_disk']['free']>=40_000_000_000
(E/'LIBB_EXPORT.json').write_text(json.dumps(out,indent=1)+'\n')
paths=[out['export']]+json.loads((E/'LIBB_PATHS.json').read_text());(E/'LIBB_EXPORT_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
print(json.dumps(dict(files=len(out['objects']),bytes=sum(x['bytes']for x in out['objects']),free=out['host_disk']['free'],deletions=0)))
