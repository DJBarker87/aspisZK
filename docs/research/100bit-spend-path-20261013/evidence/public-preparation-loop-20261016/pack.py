from pathlib import Path
import hashlib, json, tarfile, io
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-20261016/proofs-loop')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for folder in ['sources','objects','successful-targets','runs','input-manifests']:
 for p in (w/folder).rglob('*'):
  if p.is_file() and not p.is_symlink():files[str(p.relative_to(w))]=p
for name in ['runner.py','stage.py','external-inputs-loop.json','import-source-audit.json','pack.py']:
 files[name]=w/name
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())}
out=w/'public-preparation-loop.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
 x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
n='ExtractedPreparationSerializerLoop'
r=json.loads((w/'successful-targets'/f'{n}.json').read_text())
assert r['exit_status']==0 and r['axioms']['passed']
attempts={p.parent.parent.name:json.loads(p.read_text()) for p in (w/'runs').glob(f'*/{n}/receipt.json')}
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,
 'proof_base_revision':'414157881c77106966320b5725feec947b4f2add',
 'rust_helper_revision':'b92ab28465f9ffd4edcd3e2d5300cc9306ba66af',
 'module':n,'receipt':r,'attempts':attempts,
 'scope':'Exact actual full fields-loop and fields-wrapper outcome equality, including mutable vector, fail and div, with no capacity or success premise. Frontier/public serializer transport, outer caller reachability, runtime preservation and custody remain OPEN.',
 'predecessor_evidence':'../public-preparation-fields-20261016/manifest.json'}
(w/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']},indent=2))
