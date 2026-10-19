from pathlib import Path
import hashlib,json,tarfile,io
root=Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-copy-helper-proof-20261016')
a=root/'caller-adapted';p=root/'proofs';j=root/'caller'
files={}
def add(path):
 assert path.is_file() and not path.is_symlink(),path
 files[str(path.relative_to(root))]=path
def tree(path):
 for f in path.rglob('*'):
  if f.is_file() and not f.is_symlink():add(f)
for folder in ['sources','objects','successful-targets','runs','provenance']:tree(a/folder)
for filename in ['runner.py','stage.py','external-inputs-public.json','removed-decoder-pins.json']:add(a/filename)
for folder in ['sources','objects','successful-targets']:tree(p/folder)
for attempt in ['withdrawal-a','original-tags-a']:tree(p/'runs'/attempt)
for name in ['history/SOURCE-MANIFEST-before-withdrawal.json','history/withdrawal-reservation-a.json']:add(p/name)
for folder in ['sources','runs/joint-a','input-manifests']:tree(j/folder)
for name in ['runner.py','stage.py','external-inputs-caller.json','import-source-audit.json']:add(j/name)
add(root/'pack-caller.py')
mods={}
for space,w in [('adapted',a),('original',p)]:
 mm=json.loads((w/'sources/SOURCE-MANIFEST.json').read_text());mods[space]={}
 for n in mm['topological_order']:
  r=json.loads((w/'successful-targets'/(n+'.json')).read_text())
  assert r['exit_status']==0 and r['axioms']['passed'],(space,n)
  mods[space][n]=r
hashes={n:hashlib.sha256(f.read_bytes()).hexdigest() for n,f in sorted(files.items())}
out=root/'decoder-public-bridge.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,f in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(f,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode();x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
m={'format':1,'archive':out.name,'archive_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,
 'proof_base_revision':'92756a3c1098e3c1c3e2586ec303fbae20191292','rust_source_revision':'0626294e34632812accf4cb14704f027368ea871',
 'modules':mods,'joint_import_failure':json.loads((j/'runs/joint-a/DecoderCallerJoint/receipt.json').read_text()),
 'adapter_pins':json.loads((a/'provenance/adapter-pins.json').read_text()),
 'original_generated_evidence':'../terminal-decoder-432-20261016/manifest.json','outer_decoder_success_evidence':'../terminal-decoder-success-20261016/manifest.json',
 'scope':'Withdrawal-only actual ASF8 decoder success discharges existing CallerPublic.encoder_serializer_parsePublic.he via fixed nine-field/error-preserving transport. Actual semantic serializer hs, t binding to decoded transition, supplied-public equality and caller/runtime preservation remain OPEN.',
 'adapted_standard_only_reports':sum(len(r['axioms']['reports']) for r in mods['adapted'].values())}
(root/'decoder-public-bridge-manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries','adapted_standard_only_reports']},indent=2))
