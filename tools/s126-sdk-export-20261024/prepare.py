#!/usr/bin/env python3
"""Source-session CURRENT-side transport preparation; no original-side access."""
from pathlib import Path
import hashlib,json,subprocess,os
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-current-export-20261024';P.mkdir(exist_ok=True)
W=Path('/private/tmp/s126-sdk-current-export-20261024-v1');W.mkdir(mode=0o700,exist_ok=False);(W/'transport').mkdir(mode=0o700)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
request_path='evidence/port27sdk-20261024/Port27SDK_export-request.json';request_raw=subprocess.check_output(['git','show','93de4606f3:'+request_path]);request=json.loads(request_raw);assert request['current_revision']=='9acc015544c36891712af984c0a9604a39425eeb'
(P/'request.json').write_bytes(request_raw)
pins=E/'s6-sdk-first-factor-import-pins.json';m=json.loads(pins.read_text());roots=[Path('/tmp/s126-current-caller-20261021-objects')]+[Path(x) for x in Path('/tmp/s126-s6-sdk-first-path-20261024.txt').read_text().strip().split(':')]
# Verify every already selected object before the exporter can read it.
inputs=[]
for row in m['modules']:
 p=Path(row['path']);assert sha(p)==row['sha256'],str(p)
 files=[]
 for suffix in ['', '.server','.private']:
  q=Path(str(p)+suffix)
  if q.exists():files.append(dict(path=str(q),bytes=q.stat().st_size,sha256=sha(q)))
 inputs.append(dict(module=row['name'],files=files))
for n,row in request['targets'].items():
 p=B/'lean-candidates/s126-caller-boundary-20261021'/(n+'.lean');assert sha(p)==row['source']['sha256']
 source=subprocess.check_output(['git','show',request['current_revision']+':'+row['source']['path']]);assert source==p.read_bytes()
 obj=next(r/(n+'.olean') for r in roots if (r/(n+'.olean')).exists());assert sha(obj)==row['published_object_sha256']
seeds=request['primary_seeds']+['AspisS6CurrentStage1FirstFields.accepted_stage1','AspisS1ValuesOwnedInstallation.owned_stage1_account_numeric','AspisS6CurrentFirstInstallation.install','AspisS6CurrentFirstInstallation.current','AspisS6CurrentFirstInstallation.first_decoded_eq','AspisS1ValuesOwnedInstallation.withValues','AspisS1ValuesOwnedInstallation.nativeValues','AspisS1ValuesOwnedInstallation.expandValues','AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers.install','AspisS1ExtractedRoundChildren.children']
modules=['S6SdkDependencyFactorV1','S6SdkStage1ReuseFactoredV1','S1SdkStage1AccountNumericV1','S6CurrentStage1FirstFieldsV1','S1OwnedStage1AccountNumericV1','S6CurrentFirstInstallationV1','S1ValuesOwnedInstallationV1','S1NativePrepareBuffersV1','S1ExtractedRoundChildrenV1']
config=dict(schema='focused-extractor-proof-packet-v1',roots=[str(p) for p in roots],modules=modules,seeds=seeds,all_declarations=['S6SdkDependencyFactorV1'],dest=str(W/'transport'))
(W/'input.json').write_text(json.dumps(config,indent=2)+'\n');(P/'input.json').write_bytes((W/'input.json').read_bytes())
lean=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');toolroot=lean.parents[1]
tools=[lean,lean.with_name('lake')]+sorted((toolroot/'lib/lean').glob('*.dylib'))
(P/'input-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',basis=str(pins.relative_to(R)),basis_sha256=sha(pins),request_revision='93de4606f3',request_path=request_path,request_sha256=hashlib.sha256(request_raw).hexdigest(),current_source_revision=request['current_revision'],live_worktree_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),inputs=inputs,tools={str(p):dict(bytes=p.stat().st_size,sha256=sha(p)) for p in tools},lean_version=subprocess.check_output([str(lean),'--version'],text=True).strip(),scope='CURRENT selected cached objects only, freshly hash-checked against published 9acc source/receipts and selected import metadata. Dirty overlays retained as cached inputs, not attributed to Git. No original-side donor traversal or build.'),indent=2)+'\n')
print(json.dumps(dict(work=str(W),modules=len(inputs),requested_seed_count=len(seeds),tool_files=len(tools))))
