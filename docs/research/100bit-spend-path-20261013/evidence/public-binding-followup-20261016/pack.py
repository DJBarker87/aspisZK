from pathlib import Path
import hashlib,io,json,tarfile
W=Path('/home/dombarker/project-offloads/aspis-r1-public-binding-followup-20261016')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for folder in ['sources','objects','successful-targets','runs','tools']:
 for p in (W/folder).rglob('*'):
  if p.is_file() and not p.is_symlink():files[str(p.relative_to(W))]=p
for folder in ['input','runs','generated','generated-extended']:
 for p in (W/'first-diagnostic'/folder).rglob('*'):
  if p.is_file() and not p.is_symlink():files[str(p.relative_to(W))]=p
files['first-diagnostic/FirstDiagnostic.llbc']=W/'first-diagnostic/FirstDiagnostic.llbc'
for name in ['runner.py','external-inputs.json','pack.py','extended-tool-audit.json','first-a.guard.json','first-b.guard.json','first-d.launcher-failure.json','first-binder-audit.json']:files[name]=W/name
hashes={n:sha(p.read_bytes()) for n,p in sorted(files.items())}
out=W/'public-binding-followup.tar.gz'
with tarfile.open(out,'w:gz') as t:
 seen={}
 for n,p in sorted(files.items()):
  h=hashes[n]
  if h in seen:
   x=tarfile.TarInfo(n);x.type=tarfile.LNKTYPE;x.linkname=seen[h];t.addfile(x)
  else:t.add(p,arcname=n,recursive=False);seen[h]=n
 data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
 x=tarfile.TarInfo('SHA256SUMS');x.size=len(data);t.addfile(x,io.BytesIO(data))
receipts={n:json.loads((W/'successful-targets'/(n+'.json')).read_text()) for n in ['ExtractedPreparationSerializerWhole','ExtractedPublicPreparationBinding','ExtractedFirstCallerReachability']}
for r in receipts.values():assert r['exit_status']==0 and r['axioms']['passed']
m={'format':1,'archive':out.name,'archive_sha256':sha(out.read_bytes()),'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,
 'proof_source_revision':'162f2a4d0','production_source_revision':'ebe378259fb7d9c8a007eec2c8a8eb4850e549fc',
 'final_receipts':receipts,'scope':'Actual preparation serializer frontier/whole all-outcome transport and actual public_transcript helper success supply PublicBinding.hs for both variants. Fixed actual selector equality proved. Complete emitted first prefix interpreted with checked decoder+selector and explicit tx1/mark/error parameters supplies actual decoder hd and exact same-decoded supplied public. Downstream tx1-to-helper/refinement remains OPEN. No stub or opaque-global theorem is accepted. Custody is separate and not assumed.',
 'lean_attempts':{a:{p.parent.name:json.loads(p.read_text()) for p in (W/'runs'/a).glob('*/receipt.json')} for a in ['frontier-a','whole-b','helper-a','first-c','first-e']},
 'first_diagnostic_receipts':{p.parent.name:json.loads(p.read_text()) for p in (W/'first-diagnostic/runs').glob('*/receipt.json')},
 'predecessor_evidence':'../public-preparation-loop-20261016/manifest.json','failure':'frontier-a tactic parse error; corrected changed source passed whole-b. FirstDiagnostic original Aeneas Arrow unsupported; accepted pinned extended-tool replay succeeds. first-c genericerror payload typing fixed in first-e. Preflight stops before Lean and launcher syntax failure retained. No unchanged failed formal job rerun.'}
(W/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:m[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries']},indent=2))
