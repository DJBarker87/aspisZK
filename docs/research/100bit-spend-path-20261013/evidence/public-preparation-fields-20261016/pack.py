from pathlib import Path
import hashlib, json, tarfile, io
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-20261016/proofs-fields')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for folder in ['sources','objects','successful-targets','runs','input-manifests']:
 for p in (w/folder).rglob('*'):
  if p.is_file() and not p.is_symlink():files[str(p.relative_to(w))]=p
for name in ['runner.py','stage.py','external-inputs-fields.json','import-source-audit.json','pack.py']:
 files[name]=w/name
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())}
out=w/'public-preparation-fields.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
 x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
n='ExtractedPreparationSerializerFields'
r=json.loads((w/'successful-targets'/f'{n}.json').read_text())
assert r['exit_status']==0 and r['axioms']['passed']
attempts={p.parent.parent.name:json.loads(p.read_text()) for p in (w/'runs').glob(f'*/{n}/receipt.json')}
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,
 'proof_base_revision':'91e839c9c5cc7fd08a10e3b111cb8f6fe02835c7',
 'rust_helper_revision':'b92ab28465f9ffd4edcd3e2d5300cc9306ba66af',
 'module':n,'receipt':r,'attempts':attempts,
 'scope':'Fixed eleven-error map and exact actual one-step fields-loop outcome equality, including mutable vector, fail and div. Full fields-loop/frontier/public serializer transport, outer caller reachability, runtime preservation and custody remain OPEN.',
 'predecessor_evidence':'../public-preparation-naming-20261016/manifest.json'}
(w/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']},indent=2))
