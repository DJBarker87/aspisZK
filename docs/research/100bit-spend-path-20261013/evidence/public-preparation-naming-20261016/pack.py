from pathlib import Path
import hashlib,io,json,tarfile
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-20261016')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for group in ['proofs-serializer','proofs-naming-original','proofs-naming-adapted']:
 for folder in ['sources','objects','successful-targets','runs','input-manifests']:
  for p in (w/group/folder).rglob('*'):
   if p.is_file() and not p.is_symlink():files[str(p.relative_to(w))]=p
 for p in (w/group).glob('*.json'):files[str(p.relative_to(w))]=p
 for name in ['runner.py','stage.py']:files[group+'/'+name]=w/group/name
for name in ['pack-naming.py','run-naming.py','continue-naming.py','orchestration-stop.json']:files[name]=w/name
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())}
archive=w/'public-preparation-naming.tar.gz'
with tarfile.open(archive,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
 x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
receipts={}
for group in ['proofs-naming-original','proofs-naming-adapted']:
 receipts[group]={p.stem:json.loads(p.read_text()) for p in (w/group/'successful-targets').glob('*.json')}
assert sum(map(len,receipts.values()))==7
m={'format':1,'archive':archive.name,'archive_sha256':sha(archive.read_bytes()),
 'archive_bytes':archive.stat().st_size,'archive_entries':len(files)+1,
 'producing_original_extension':'9cf712b0504622c2068ac5948a6244db15071552',
 'rust_source':'b92ab28465f9ffd4edcd3e2d5300cc9306ba66af','lean_receipts':receipts,
 'scope':'Names-only five-instance new common Types overlay. Original/adapted28 tags, unchanged Funs7actual roots and CSuccess3 exports; original failed joint import retained. No old serializer/protocol proof replay, Rust/runtime or outer-caller closure.',
 'original_joint_failure':json.loads((w/'proofs-serializer/runs/joint-a/PreparationSerializerJoint/receipt.json').read_text())}
(w/'manifest-naming.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']},indent=2))
