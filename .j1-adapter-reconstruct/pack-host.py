from pathlib import Path
import hashlib,json,tarfile,io
root=Path('/home/dombarker/project-offloads/aspis-r1-j1a-adapter-reconstruct-20261016')
files={}
for rel in ['input','extraction-a','runs','preparation-2b51','proofs/sources','proofs/objects','proofs/successful-targets','proofs/runs','compat-inputs']:
 for p in (root/rel).rglob('*'):
  if p.is_file() and not p.is_symlink(): files[str(p.relative_to(root))]=p
for rel in ['pack-host.py','run-host.py','proofs/runner.py','metadata-preflight.json','selected-dependency-preflight.json','repository-source-pins.json','source-equivalence.json']:
 files[rel]=root/rel
files['tool-pins/tools-final-pins.json']=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/tools-final-pins.json')
files['tool-pins/backend-final-manifest.json']=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend-final-manifest.json')
hashes={n:hashlib.sha256(p.read_bytes()).hexdigest() for n,p in sorted(files.items())}
sums=''.join(f'{h}  {n}\n' for n,h in hashes.items()).encode()
with tarfile.open(root/'package-host.tar.gz','w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   info=tarfile.TarInfo(n);info.type=tarfile.LNKTYPE;info.linkname=seen[h];t.addfile(info)
  else:
   t.add(p,arcname=n,recursive=False);seen[h]=n
 info=tarfile.TarInfo('SHA256SUMS');info.size=len(sums);t.addfile(info,io.BytesIO(sums))
print(json.dumps({'archive':'package-host.tar.gz','entries':len(files)+1,'bytes':(root/'package-host.tar.gz').stat().st_size,'sha256':hashlib.sha256((root/'package-host.tar.gz').read_bytes()).hexdigest()}))
