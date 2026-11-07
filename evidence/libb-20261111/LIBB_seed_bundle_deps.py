"""Retain missing unchanged objects from the merged bundle's pinned seeds."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
own=json.loads((E/'LIBB_PATHS.json').read_text())
source=json.loads((E.parent/'lib-20261111'/'LIB_PATHS.json').read_text())
new=[p for p in source if p not in own]
code='''from pathlib import Path
import hashlib,json,shutil
roots=[Path(p) for p in %r];sources=[Path(p) for p in %r]
dest=Path('/home/dombarker/project-offloads/codex-cx-libb-20261111/LIBB_seedBundleDeps');files=[]
for source in sources:
 for p in sorted(source.rglob('*.olean')):
  rel=p.relative_to(source)
  if any((r/rel).is_file() for r in roots) or (dest/rel).exists():continue
  for suffix in ['', '.private','.server']:
   z=Path(str(p)+suffix)
   if not z.is_file():continue
   q=Path(str(dest/rel)+suffix);q.parent.mkdir(parents=True,exist_ok=True)
   h=hashlib.sha256(z.read_bytes()).hexdigest();shutil.copy2(z,q)
   assert hashlib.sha256(q.read_bytes()).hexdigest()==h
   files.append(dict(source=str(z),destination=str(q),sha256=h,bytes=q.stat().st_size))
  z=p.with_suffix('.ir')
  if z.exists():
   q=(dest/rel).with_suffix('.ir');h=hashlib.sha256(z.read_bytes()).hexdigest();shutil.copy2(z,q)
   assert hashlib.sha256(q.read_bytes()).hexdigest()==h
   files.append(dict(source=str(z),destination=str(q),sha256=h,bytes=q.stat().st_size))
print(json.dumps(dict(sources=[str(p) for p in sources],destination=str(dest),files=files,disk=shutil.disk_usage(dest)._asdict())))
'''%(['/home/dombarker/project-offloads/codex-cx-libb-20261111/LIBB_objects']+own,new)
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 with (E/'LIBB_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(event='seed_bundle_missing_dependencies',retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert x['disk']['free']>=40_000_000_000
(E/'LIBB_BUNDLE_DEPS_REUSE.json').write_text(json.dumps(x,indent=1)+'\n')
if x['destination'] not in own:own.insert(1,x['destination']);(E/'LIBB_PATHS.json').write_text(json.dumps(own,indent=1)+'\n')
print(json.dumps(dict(files=len(x['files']),bytes=sum(y['bytes']for y in x['files']),free=x['disk']['free'])))
