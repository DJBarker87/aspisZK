"""Retain all proof inputs by content hash; only remove duplicated source snapshots."""
from pathlib import Path
import json,lzma,hashlib,shutil
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry4-20261106'
sha=lambda b:hashlib.sha256(b).hexdigest()
idx=json.loads((E/'NIJ_INPUTS.json').read_text()) if (E/'NIJ_INPUTS.json').exists() else dict(objects={},attempts={})
prior=json.loads((P/'NHY_INPUTS.json').read_text())
finished={p.parent.name for p in E.glob('NIJ_*/receipt.json')}
for p in sorted(E.glob('NIJ_*/sources/**/*')):
 if not p.is_file() or p.relative_to(E).parts[0] not in finished:continue
 assert p.suffix in ['.rs','.lean','.json','.py','.c','.lock'] or p.name=='Cargo.lock',p
 assert not any(t in p.name.lower() for t in ['wallet','keypair','secret']),p
 raw=p.read_bytes();h=sha(raw)
 if h in prior['objects']:
  q=P/prior['objects'][h]['path'];data=lzma.decompress(q.read_bytes());assert data==raw
  path='../slice-d-entry4-20261106/'+prior['objects'][h]['path']
 else:
  q=E/'NIJ_INPUTS'/(h+'.xz');q.parent.mkdir(exist_ok=True)
  if not q.exists():q.write_bytes(lzma.compress(raw))
  path=str(q.relative_to(E))
 idx['objects'][h]=dict(path=path,bytes=len(raw),archive_sha256=sha(q.read_bytes()))
 attempt=p.relative_to(E).parts[0];rel=str(p.relative_to(E/attempt/'sources'));idx['attempts'].setdefault(attempt,{})[rel]=h
 p.unlink()
for p in sorted(E.glob('NIJ_*/sources/**/*'),reverse=True):
 if p.is_dir() and not any(p.iterdir()):p.rmdir()
for h,r in idx['objects'].items():
 q=E/r['path'];assert sha(q.read_bytes())==r['archive_sha256'];assert sha(lzma.decompress(q.read_bytes()))==h
(E/'NIJ_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
for p in E.rglob('__pycache__'):shutil.rmtree(p)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
print(json.dumps(dict(attempts=len(idx['attempts']),objects=len(idx['objects']),own_archive_bytes=sum(p.stat().st_size for p in (E/'NIJ_INPUTS').glob('*.xz')))))
