from pathlib import Path
import hashlib,io,json,tarfile
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-tx1-actual-20261016');sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for p in W.rglob('*'):
 n=str(p.relative_to(W))
 if p.is_file() and not p.is_symlink() and n.split('/')[0] in ['input','runs','generated','run-host.py','reservations.txt','VerifyPreparedPrefix.llbc']:files['actual-tx1/'+n]=p
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())};out=W/'tx1-caller-blocker.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode();x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
r={str(p.parent.name):json.loads(p.read_text()) for p in (W/'runs').glob('*/receipt.json')};assert r['charon-b']['exit_status']==0 and r['aeneas-b']['exit_status']==2
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,'production_revision':'3335eecf2f2a08096abe95c67ac6b304f2df6284','receipts':r,'scope':'Complete unchanged actual tx1 and mark; actual approved Prepared body; named explicit source boundaries. Valid Charon LLBC; Aeneas rejects actual query while before emission. No Lean/proof/axioms result claimed. No rewrite probe or adoption.','print_axioms':'N/A: no Lean result; Aeneas did not emit.','additional_cone':{'llbc':'actual-tx1/VerifyPreparedPrefix.llbc','source_pins':'actual-tx1/input/source-pins.json','source_kit':'actual-tx1/input/lib.rs'}}
(W/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']}))
