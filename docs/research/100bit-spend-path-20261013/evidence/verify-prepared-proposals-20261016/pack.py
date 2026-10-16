from pathlib import Path
import hashlib,io,json,tarfile
W=Path('/home/dombarker/project-offloads');O=W/'aspis-r1-worker-c-verify-prepared-evidence-20261016';O.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
roots={
'actual':'aspis-r1-worker-c-verify-prepared-cut-20261016',
'verify-while':'aspis-r1-worker-c-verify-proposal-while-20261016',
'verify-straight':'aspis-r1-worker-c-verify-proposal-straight-20261016',
'verify-straight-closure':'aspis-r1-worker-c-verify-proposal-straight-closure-20261016',
'prepared-owned':'aspis-r1-worker-c-prepared-proposal-owned-20261016',
'prepared-helper':'aspis-r1-worker-c-prepared-proposal-helper-20261016',
'prepared-helper-fields':'aspis-r1-worker-c-prepared-proposal-helper-fields-20261016',
'verify-round-helper':'aspis-r1-worker-c-verify-proposal-round-helper-20261016',
'verify-round-helper-mask':'aspis-r1-worker-c-verify-proposal-round-helper-mask-20261016'}
files={};receipts={}
for label,root in roots.items():
 w=W/root
 for p in w.rglob('*'):
  rel=p.relative_to(w)
  if p.is_file() and not p.is_symlink() and rel.parts[0] in ['input','runs','generated','run-host.py','reservations.txt','VerifyPreparedPrefix.llbc']:
   files[label+'/'+str(rel)]=p
   if p.name=='receipt.json':receipts[label+'/'+str(rel)]=json.loads(p.read_text())
assert receipts['prepared-helper-fields/runs/aeneas-a/receipt.json']['exit_status']==0
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())};out=O/'verify-prepared-proposals.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode();x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,'production_revision':'c16ab4d76619cf2cf80ece9d7e60e47975957af0','scope':'Extraction diagnostics only. actual roots preserve complete current caller bodies over explicit named source boundaries; all proposals are separate unapproved source inputs. No Lean proof, axioms audit, runtime, SBF or production adoption in this evidence. Every future theorem must eliminate opaque globals via explicit arguments or checked definitions. Custody separate.','print_axioms':'N/A: no Lean result or compilation asserted by this extraction-only bundle.','receipts':receipts,'roots':roots}
(O/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']}))
