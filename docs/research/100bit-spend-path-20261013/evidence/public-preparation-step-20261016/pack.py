#!/usr/bin/env python3
"""Archive immutable extraction and its original three-target Lean gate."""
from pathlib import Path
import hashlib, io, json, tarfile
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-step-20261016')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for folder in ['input','generated','runs','proofs/sources','proofs/objects',
               'proofs/successful-targets','proofs/runs']:
 for p in (w/folder).rglob('*'):
  if p.is_file() and not p.is_symlink():files[str(p.relative_to(w))]=p
for name in ['PublicPreparation.llbc','output-audit.json','run-host.py','pack.py','compare-original.py','original-definition-comparison.json','root-selection-audit.json',
             'proofs/runner.py','proofs/stage.py','proofs/external-inputs.json']:
 files[name]=w/name
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())}
archive=w/'public-preparation-extraction.tar.gz'
with tarfile.open(archive,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
 x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
targets=['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','PublicPreparationActualAudit','ExtractedPublicPreparationSuccess']
manifest={'format':1,'archive':archive.name,'archive_sha256':sha(archive.read_bytes()),
 'archive_bytes':archive.stat().st_size,'archive_entries':len(files)+1,
 'source_revision':'b92ab28465f9ffd4edcd3e2d5300cc9306ba66af',
 'features':['r0','private-leaf-salts'],'cuts':30,'full_repository_source_files':12,
 'extraction_receipts':{n:json.loads((w/'runs'/n/'receipt.json').read_text()) for n in ['charon-a','aeneas-a']},
 'lean_receipts':{n:json.loads((w/'proofs/successful-targets'/(n+'.json')).read_text()) for n in targets},
 'scope':'Actual four helper roots, reused serializer and generic Digest32 constructor. Seven actual declarations and three re-pinned helper-success theorems audited standard-only. No claim for derived Debug methods, Rust/backend preservation, outer caller reachability, runtime digest semantics or custody.',
 'inventory':'output-audit.json retains all 43 LLBC opaque functions and 66 source-file content pins; no generated external template or opaque function.'}
(w/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:manifest[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']},indent=2))
