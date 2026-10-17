from pathlib import Path
import hashlib,io,json,tarfile
B=Path('/home/dombarker/project-offloads');W=B/'aspis-r1-worker-c-tx1-proof-20261016';sha=lambda b:hashlib.sha256(b).hexdigest();files={}
for label,root in [('proof',W),('tx1-finish-diagnostic',B/'aspis-r1-worker-c-tx1-finish-20261016'),('tx1-actual-accumulator',B/'aspis-r1-worker-c-tx1-accumulator-20261016')]:
 for p in root.rglob('*'):
  rel=p.relative_to(root)
  if p.is_file() and not p.is_symlink() and rel.parts[0] in ['sources','objects','successful-targets','runs','input','generated','VerifyPreparedPrefix.llbc','runner.py','run-host.py','serial-proof-host.py','stage-host.py','external-inputs.json','excluded-old-universe.json','guard-events.json']:
   files[label+'/'+str(rel)]=p
receipts={p.stem:json.loads(p.read_text()) for p in (W/'successful-targets').glob('*.json')};assert len(receipts)==5
for r in receipts.values():assert r['exit_status']==0 and r['axioms']['passed']
assert sum(len(r['axioms']['reports']) for r in receipts.values())==18
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())};out=W/'tx1-caller-accepted.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode();x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,'production_revision':'e5c186ba3bcbbf9a0cc5878077aa8848853a65cc','formal_receipts':receipts,'scope':'Complete actual approved tx1+Accumulator constructor+observer dispatch/error closure model and success inversion. Five explicit function boundaries plus six Prepared boundaries; no opaque global. Reaches named verify boundary and actual Prepared model. Actual verify→public_transcript, complete25 sourcebytes/hread, query/checkpoint tail refinement, SDK and custody remain OPEN.','additional_cone':{'label':'actual-tx1-accumulator','llbc':'tx1-actual-accumulator/VerifyPreparedPrefix.llbc','source_pins':'tx1-actual-accumulator/input/source-pins.json','source_kit':'tx1-actual-accumulator/input/lib.rs'},'guard_policy':'Prior own Type killed on external arrival retained; corrected serial process reuses verified import hash/stat snapshot across targets; latest external arrival suppressed before actualPopen (own_pid:null). No external job signalled.','failure_scope':'All failed proof/staging receipts retained; only successful-targets are release results.'}
(W/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']}))
