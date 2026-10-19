from pathlib import Path
import hashlib, json, tarfile, io
w=Path('/home/dombarker/project-offloads/aspis-r1-digest32-transcript-proof-20261016')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for folder in ['sources','objects','successful-targets','runs','input-manifests']:
 for p in (w/folder).rglob('*'):
  if p.is_file() and not p.is_symlink():files[str(p.relative_to(w))]=p
for name in ['runner.py','stage.py','external-inputs-proof.json','import-source-audit.json','pack.py']:
 files[name]=w/name
# Retain the two exact producing receipts/sources/objects without replay.
for entry in json.loads((w/'import-source-audit.json').read_text()):
 name=entry['module'];rp=Path(entry['receipt']);receipt=json.loads(rp.read_text())
 stem=name.replace('.','/')
 files['imports/'+stem+'/receipt.json']=rp
 files['imports/'+stem+'/source.lean']=rp.parent.parent/'sources'/(stem+'.lean')
 for suffix,obj in receipt['objects'].items():files['imports/'+stem+'/object'+suffix]=Path(obj['path'])
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())}
out=w/'digest32-transcript-proof.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
 x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
r=json.loads((w/'successful-targets/ExtractedDigest32Transcript.json').read_text())
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,
 'proof_base_revision':'9cf712b0504622c2068ac5948a6244db15071552',
 'rust_helper_revision':'b92ab28465f9ffd4edcd3e2d5300cc9306ba66af',
 'module':'ExtractedDigest32Transcript','receipt':r,
 'scope':'Actual constructor and admitted validated-step normal form/success carry. Five standard-only reports; failed first attempt retained. Naming-adapted two-module input from exact producing receipts. No full33 caller, runtime effects or syscall refinement.',
 'predecessor_scope':'C separate naming-adapted common Types/Funs; exact imported receipts/sources/objects retained under imports/'}
(w/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']},indent=2))
