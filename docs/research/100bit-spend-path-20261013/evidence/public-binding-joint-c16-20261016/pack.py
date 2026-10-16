from pathlib import Path
import hashlib,io,json,tarfile
W=Path('/home/dombarker/project-offloads/aspis-r1-public-binding-joint-c16-20261016')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for folder in ['sources','objects','successful-targets','runs','raw-current']:
 for p in (W/folder).rglob('*'):
  if p.is_file() and not p.is_symlink():files[str(p.relative_to(W))]=p
for name in ['runner.py','stage.py','external-inputs.json','excluded-old-universe.json','adapter-pins.json','pack.py','resume-joint.py','resume-record.json']:files[name]=W/name
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())}
out=W/'public-binding-joint-c16.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode();x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
receipts={p.stem:json.loads(p.read_text()) for p in (W/'successful-targets').glob('*.json')};assert len(receipts)==8
for r in receipts.values():assert r['exit_status']==0 and r['axioms']['passed']
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,'proof_source_revision':'162f2a4d0','current_caller_source_revision':'c16ab4d76','final_receipts':receipts,'scope':'Two current actual caller generated modules with only five naming expansions and six C dependent proof modules, one coherent current universe;79original declarations unchanged. Old universe and every reverse importer removed from external cache.19standard-only axiom reports. No package replay, SBF or runtime run.','attempts':[p.name for p in sorted((W/'runs').iterdir()) if p.is_dir()],'failures':'joint-a Types green then overlay old/current name conflict; removed full old reverse-import closure and reused same greenTypes key. joint-b ownWhole killed when externalLean1667533 arrived, predecessors reused; joint-c similarly interrupted by externalLean1669402. Focused in-process resume verifies external snapshot once and retains every per-target stat/source/object check; all interrupted targets are distinct retained attempts.'}
(W/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:m[k] for k in ['archive_sha256','archive_bytes','archive_entries']},indent=2))
