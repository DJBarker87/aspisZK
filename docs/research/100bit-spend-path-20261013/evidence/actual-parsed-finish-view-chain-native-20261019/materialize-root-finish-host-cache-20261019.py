from pathlib import Path
import json,hashlib,tarfile
root=Path('/tmp/root-finish-view-host-cache-20261019');root.mkdir(exist_ok=False)
with tarfile.open('/tmp/root-finish-view-host-missing-20261019.tar.gz') as t:t.extractall(root,filter='data')
rows=json.loads(Path('/tmp/root-finish-view-host-manifest-20261019.json').read_text())
for r in rows:
 dst=root/'objects'/Path(*r['module'].split('.')).with_suffix('.olean')
 if r['existing']:
  src=Path(r['existing']);assert hashlib.sha256(src.read_bytes()).hexdigest()==r['sha256'],str(src)
  dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src)
  for suffix in ['.private','.server']:
   a=Path(str(src)+suffix);b=Path(str(dst)+suffix)
   if a.is_file():b.symlink_to(a)
  a=src.with_suffix('.ir');b=dst.with_suffix('.ir')
  if a.is_file():b.symlink_to(a)
 else:assert hashlib.sha256(dst.read_bytes()).hexdigest()==r['sha256'],str(dst)
print('exact pinned objects ready',len(rows))
