from pathlib import Path
import hashlib, json, tarfile, io
w=Path('/home/dombarker/project-offloads/aspis-r1-caller-binding-20261016')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for folder in ['sources','objects','successful-targets','runs','input-manifests']:
 for p in (w/folder).rglob('*'):
  if p.is_file() and not p.is_symlink():files[str(p.relative_to(w))]=p
for name in ['runner.py','stage.py','external-inputs-binding.json','import-source-audit.json','pack.py']:
 files[name]=w/name
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())}
out=w/'decoder-public-binding.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
 x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
r=json.loads((w/'successful-targets/ExtractedDecoderPublicBinding.json').read_text())
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,
 'proof_base_revision':'ca137f5db50123d6157ce144e43e4f15d8fad94b',
 'rust_decoder_revision':'0626294e34632812accf4cb14704f027368ea871',
 'module':'ExtractedDecoderPublicBinding','receipt':r,
 'scope':'Fixed full transition and both-variant projection; actual hd/hs remain premises. Semantic parse equals computed fixed source projection without hbind. Actual caller identification, runtime/extraction preservation and custody remain OPEN.',
 'predecessor_evidence':'../decoder-public-bridge-20261016/manifest.json'}
(w/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']},indent=2))
