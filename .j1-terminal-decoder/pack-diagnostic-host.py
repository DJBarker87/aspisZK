from pathlib import Path
import hashlib,json,tarfile,io
roots={'layout80':Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-proof-20261016'), 'geometry1024':Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-geometry-proof-20261016')}
files={}
for label,root in roots.items():
 for rel in ['original','diagnosis','proofs/sources','proofs/objects','proofs/successful-targets','proofs/runs']:
  if not (root/rel).exists():continue
  for p in (root/rel).rglob('*'):
   if p.is_file() and not p.is_symlink():files[label+'/'+str(p.relative_to(root))]=p
 files[label+'/proofs/runner.py']=root/'proofs/runner.py'
out=roots['layout80']/'decoder-diagnostic.tar.gz'
hashes={n:hashlib.sha256(p.read_bytes()).hexdigest() for n,p in sorted(files.items())}
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   m=tarfile.TarInfo(n);m.type=tarfile.LNKTYPE;m.linkname=seen[h];t.addfile(m)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode();m=tarfile.TarInfo('SHA256SUMS');m.size=len(data);t.addfile(m,io.BytesIO(data))
print(json.dumps({'archive':out.name,'entries':len(files)+1,'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))
