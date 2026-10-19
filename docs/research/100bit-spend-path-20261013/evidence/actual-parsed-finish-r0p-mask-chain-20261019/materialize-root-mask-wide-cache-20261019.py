from pathlib import Path
import tarfile,json,hashlib
old=Path('/tmp/root-finish-view-host-cache-20261019/objects');root=Path('/tmp/root-mask-wide-native-cache-20261019');root.mkdir(exist_ok=False)
with tarfile.open('/tmp/root-mask-wide-extra-objects-20261019.tar.gz') as t:t.extractall(root,filter='data')
new=root/'objects'
for f in old.rglob('*'):
 if f.is_file():
  d=new/f.relative_to(old)
  if not d.exists():d.parent.mkdir(parents=True,exist_ok=True);d.symlink_to(f)
for x in json.loads(Path('/tmp/root-mask-wide-extra-objects-20261019.json').read_text()):
 f=new/Path(*x['module'].split('.')).with_suffix('.olean');assert hashlib.sha256(f.read_bytes()).hexdigest()==x['sha256'],x['module']
print('coherent prior closure +12 new modules ready')
